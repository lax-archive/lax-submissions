import Lax3Proofs.SolveSegPrep

/-!
# F6c11a (part 1) — the child-building pass: the assembly seam, discharged

`SolveSegPrep` named **`ChildLoad`** — the machine pass that builds the
child of centre `u` in the level-`(j+1)` regions, concluding the
windowed contract at `Impl.ofArena (childArena S A π u) (htabF (j+1) …)`.
Its discharge composes the landed stage lifts (`restrictCom_specW`,
`bfsCom_specW`, `supportsCom_specW`, `profilesCom_specW`,
`isolateCom_specW`) with new IMP+ glue (the cluster-row read, the batch
assembly, the colour-region writer). What those stages *deliver*, read
off their postconditions, is not literally `ofArena childArena` — it is
the machine's own assembly:

* a CSR at the **isolated restricted graph**
  (`isolateCom_specW` at `W = range batchFn` over `restrict`'s graph);
* a colour region at **`recordProfilesMS`** — the slot colouring
  thresholded off the pd/pu tables `profilesCom_specW` leaves
  (`Impl.ProfileTablesMS` at the PRE-isolation child `preG`, the
  campaign's oldest hazard);
* a renaming region at `restrict`'s composite `up`;
* a channel region at the **supports-written `descendCol` table** —
  one `supportsCom_specW` call per round `e`, each recomputing column
  `e` as the gradient-walk lists of that round's ball table at radius
  `2R` in `preG`.

This file discharges the **assembly seam** between that machine shape
and `ChildLoad`'s verbatim conclusion, so that the remaining work is
exactly the stage composition and nothing semantic:

* **`machChild`** names the assembled machine arena (§3), and
  **`machChild_eq_ofArena`** proves it *is*
  `Impl.ofArena (childArena S A π u) chan` — the graph, carrier and
  renaming identities are `ImplRestrict`'s definitional seams
  (`childArena_G_eq_isolate_restrict`, `restrict_up_eq_childArena_up`),
  and the colour identity is the landed
  `Impl.recordProfilesMS_eq_childCol` under the `ProfileTablesMS` seam.
* **`ChildLoadParts`** (§4) is the named machine residual restated at
  the parts: the same `Spec` as `ChildLoad` — same precondition, same
  frame clauses, same budget slot — with the windowed contract stated
  at `machChild` (the shape the composed stages hand over, the
  `ProfileTablesMS` witness carried existentially) and the channel at
  an explicit table family `chanF`. **`childLoad_of_parts`** and
  **`childLoadAll_of_parts`** conclude verbatim
  `ChildLoad`/`ChildLoadAll` from it, given the one seam hypothesis
  `hhtab : htabF (j+1) (childArena …) = chanF j A u` — F7-suppliable
  by construction, since `htabF` is F7's own parameter (see the note
  below). `centrePrepAll_of_parts` wires the corollary through
  `SolveSegPrep` to verbatim `CentrePrepAll`.

## The `htabF` note, made formal (§1–§2)

`htabF` is a free parameter of the whole chain (`ProgDriver`: it enters
only the charge); the pass *produces* a definite channel — the
supports-written `descendCol` table — and F7 must instantiate
`htabF (j+1)` to exactly that. Two facts make the instantiation
well-defined:

* **The table is canonical** (§1): `ballDist H s d` is *the* truncated
  distance table — `ballTable_eq_ballDist` shows any table satisfying
  `Impl.BallTable` with the `≤ d+1` bound (verbatim `bfsCom_specW`'s
  deliverable) equals it — so the per-round columns the pass stores are
  `descendTab H d src` (§2) regardless of which run produced them
  (`descendCol_eq_descendTab`).
* **`preG` is recoverable from the child arena alone** (§2,
  `preG_eq_comap_childUp`): the pre-isolation graph the walks live in
  is the comap of the channel head's root-mapped parent graph along the
  child's own `up` — so `htabF (j+1)` *can* be defined as a function of
  the child arena, as its type requires, with the per-round sources
  read off the same channel head. F7 owns that definition; this file
  pins the target it must hit.

## Hazards honoured

* Profiles are measured in **`preG`, before isolation** —
  `ChildLoadParts` carries the `ProfileTablesMS` witness at `preG`
  verbatim, so a discharger that measured them after isolation cannot
  meet the seam (the identity to `childCol` would be unavailable).
* The batch is the **padded** `batchFn` (width exactly `S.width`,
  duplicates included) — the `ProfileTablesMS` witness is indexed by
  `Fin S.width`, one table per padded slot.
* The supports rounds recompute **every** column in `preG` (one
  `supportsCom_specW` call per round; within one call the other
  columns are inherited) — `chanF` is one table family for all rounds,
  not a per-round patch.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.WalkDistance

variable {L n₀ : ℕ}

/-! ## §1 The canonical truncated distance table -/

open Classical in
/-- **The canonical truncated distance table** of one source at cap
`d`: the least radius reaching `v`, or `d + 1` beyond the horizon —
the unique table `bfsCom` can leave (`ballTable_eq_ballDist`). -/
noncomputable def ballDist {N : ℕ} (H : SimpleGraph (Fin N)) (s : Fin N)
    (d : ℕ) (v : Fin N) : ℕ :=
  if v ∈ ball H d s then sInf {k | v ∈ ball H k s} else d + 1

open Classical in
/-- The canonical table respects the horizon bound — the `≤ d + 1`
clause of `bfsCom_specW`'s deliverable. -/
theorem ballDist_le {N : ℕ} (H : SimpleGraph (Fin N)) (s : Fin N) (d : ℕ)
    (v : Fin N) : ballDist H s d v ≤ d + 1 := by
  rw [ballDist]
  by_cases hv : v ∈ ball H d s
  · rw [if_pos hv]
    exact le_trans (Nat.sInf_le hv) (Nat.le_succ d)
  · rw [if_neg hv]

open Classical in
/-- The canonical table is a `BallTable` — the other half of
`bfsCom_specW`'s deliverable. -/
theorem ballDist_ballTable {N : ℕ} (H : SimpleGraph (Fin N)) (s : Fin N)
    (d : ℕ) : Impl.BallTable H s d (ballDist H s d) := by
  intro v k hk
  by_cases hv : v ∈ ball H d s
  · rw [ballDist, if_pos hv]
    constructor
    · intro hle
      have hmem : v ∈ ball H (sInf {k | v ∈ ball H k s}) s :=
        Nat.sInf_mem (⟨d, hv⟩ : {k | v ∈ ball H k s}.Nonempty)
      exact ball_mono_radius H s hle hmem
    · intro hkm
      exact Nat.sInf_le hkm
  · rw [ballDist, if_neg hv]
    constructor
    · intro h
      exact absurd hk (by omega)
    · intro hkm
      exact absurd (ball_mono_radius H s hk hkm) hv

open Classical in
/-- **Uniqueness**: any table satisfying `BallTable` with the horizon
bound — verbatim what `bfsCom_specW` leaves in the distance region —
*is* the canonical table. This is what makes the pass's stored channel
independent of the run that produced it. -/
theorem ballTable_eq_ballDist {N : ℕ} {H : SimpleGraph (Fin N)}
    {s : Fin N} {d : ℕ} {D : Fin N → ℕ} (hD : Impl.BallTable H s d D)
    (hle : ∀ v, D v ≤ d + 1) : D = ballDist H s d := by
  funext v
  by_cases hv : v ∈ ball H d s
  · rw [ballDist, if_pos hv]
    have h1 : D v ≤ d := (hD v d le_rfl).mpr hv
    have h2 : v ∈ ball H (D v) s := (hD v (D v) h1).mp le_rfl
    have h3 : sInf {k | v ∈ ball H k s} ≤ D v := Nat.sInf_le h2
    have hmem : v ∈ ball H (sInf {k | v ∈ ball H k s}) s :=
      Nat.sInf_mem (⟨d, hv⟩ : {k | v ∈ ball H k s}.Nonempty)
    have h4 : D v ≤ sInf {k | v ∈ ball H k s} :=
      (hD v _ (le_trans h3 h1)).mpr hmem
    omega
  · rw [ballDist, if_neg hv]
    have h1 : ¬ D v ≤ d := fun h => hv ((hD v d le_rfl).mp h)
    have h2 := hle v
    omega

/-! ## §2 The pass's channel table, canonically -/

open Classical in
/-- **The supports-written channel table**, canonically: per round `e`,
the `descendCol` column of the round's canonical ball table at cap `d`
from the round's source. This is the table the per-round
`supportsCom_specW` calls leave in the child's channel region —
`descendCol_eq_descendTab` below — and hence the target F7's
`htabF (j+1)` must hit. -/
noncomputable def descendTab {N ℓc : ℕ} (H : SimpleGraph (Fin N)) (d : ℕ)
    (src : Fin ℓc → Fin N) : Fin N → Fin ℓc → List (Fin N) :=
  fun v e => descendCol H (ballDist H (src e) d) d v

open Classical in
/-- **The stored columns are canonical**: whatever ball tables the
per-round BFS runs actually produced (each `BallTable` + horizon bound,
verbatim `bfsCom_specW`'s deliverable), the `descendCol` columns the
supports calls store are exactly `descendTab`. -/
theorem descendCol_eq_descendTab {N ℓc : ℕ} {H : SimpleGraph (Fin N)}
    {d : ℕ} {src : Fin ℓc → Fin N} {D : Fin ℓc → Fin N → ℕ}
    (hD : ∀ e, Impl.BallTable H (src e) d (D e))
    (hle : ∀ e v, D e v ≤ d + 1) :
    (fun v e => descendCol H (D e) d v) = descendTab H d src := by
  funext v e
  show descendCol H (D e) d v = descendCol H (ballDist H (src e) d) d v
  rw [ballTable_eq_ballDist (hD e) (hle e)]

/-- **`preG` from the child arena alone** — the F7 enabler: the
pre-isolation graph the channel's walks live in is the comap, along the
child's own root renaming, of the root-mapped parent graph that the
child's channel head records (`childArena_hist`:
`Bc.hist.head = (A.up u, SimpleGraph.map A.up A.G)`). So a function of
the child arena — which is what `htabF (j+1)`'s type requires — can
reconstruct `preG` and with it the canonical channel table. -/
theorem preG_eq_comap_childUp (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    preG S A π u
      = SimpleGraph.comap (fun a => ((childArena S A π u).up a : Fin n₀))
          (SimpleGraph.map A.up A.G) := by
  have hup : ∀ z : Fin (childN S A π u),
      (childArena S A π u).up z = A.up ((childEquiv S A π u) z : Fin A.N) :=
    fun z => rfl
  ext a b
  show A.G.Adj ((childEquiv S A π u) a : Fin A.N)
      ((childEquiv S A π u) b : Fin A.N) ↔ _
  simp only [SimpleGraph.comap_adj, SimpleGraph.map_adj, hup]
  constructor
  · intro h
    exact ⟨_, _, h, rfl, rfl⟩
  · rintro ⟨x, y, hxy, hx, hy⟩
    rw [← A.up.injective hx, ← A.up.injective hy]
    exact hxy

/-! ## §3 The assembled machine arena, and the assembly identity -/

/-- **The machine's assembled child** — the arena the composed stage
lifts hand over, field by field: the cluster's carrier, the isolated
restricted graph (`isolateCom_specW`'s CSR at `W = range batchFn`,
which is `childArena`'s graph on the nose), the slot colouring
thresholded off the profile tables (`recordProfilesMS` at the pd/pu
tables `profilesCom_specW` leaves), `restrict`'s composite renaming
(= `childArena`'s, definitionally), and the supports-written channel
`chan`. -/
noncomputable def machChild (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {ℓc : ℕ}
    (Dp : Fin S.width → Fin (childN S A π u) → ℕ)
    (Dc : Fin (relPal Λ) → Fin (childN S A π u + 1) → ℕ)
    (chan : Fin (childN S A π u) → Fin ℓc → List (Fin (childN S A π u))) :
    Impl.MArena (isoPal (relPal Λ) S.width S.R) n₀ ℓc :=
  ⟨childN S A π u, (childArena S A π u).G,
    Impl.recordProfilesMS S.R (childColR S A π u) Dp Dc,
    (childArena S A π u).up, chan⟩

/-- **The assembly identity** — the seam this file exists for: under
the `ProfileTablesMS` witness at the pre-isolation child (graph `preG`,
padded batch `batchFn`, marker-extended classes `childColR` — verbatim
`profilesCom_specW`'s deliverable at the restricted child), the
machine's assembled child **is** `Impl.ofArena (childArena S A π u)`
at the same channel. Carrier, graph and renaming are definitional
(`ImplRestrict`'s seam identities); the colours are the landed
`recordProfilesMS_eq_childCol`. -/
theorem machChild_eq_ofArena (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {ℓc : ℕ}
    {Dp : Fin S.width → Fin (childN S A π u) → ℕ}
    {Dc : Fin (relPal Λ) → Fin (childN S A π u + 1) → ℕ}
    (chan : Fin (childN S A π u) → Fin ℓc → List (Fin (childN S A π u)))
    (h : Impl.ProfileTablesMS (preG S A π u) (batchFn S A π u)
      (childColR S A π u) S.R Dp Dc) :
    machChild S A π u Dp Dc chan
      = Impl.ofArena (childArena S A π u) chan := by
  unfold machChild Impl.ofArena
  rw [Impl.recordProfilesMS_eq_childCol S A π u h]
  rfl

/-! ## §4 The named residual at the parts, and the composition -/

open Classical in
/-- **The child-building pass, at the parts** (named machine residual):
`ChildLoad`'s `Spec` — same precondition, same frame clauses, same
budget slot — with the deliverable stated at the shape the composed
stage lifts actually hand over: the windowed contract at the assembled
`machChild`, its `ProfileTablesMS` witness carried existentially (the
discharger holds it as `profilesCom_specW`'s postcondition), and the
channel at the explicit table family `chanF` (the discharger's — the
supports-written `descendTab`, §2). -/
def ChildLoadParts (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
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
        (∀ y ∈ ctrName j :: levelScalars j, σ'.vars y = σ.vars y) ∧
        (∀ a ∈ ca j :: co j :: cm j :: levelArrays j,
          σ'.arrs a = σ.arrs a) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (KP k j A (u : ℕ))

open Classical in
/-- **Verbatim `ChildLoad`, from the parts**: the assembly identity
converts the parts' windowed contract to `ChildLoad`'s, under the one
seam hypothesis pinning `htabF (j+1)` at the child to the pass's own
channel table — F7-suppliable, since `htabF` is F7's parameter and §2
gives the canonical target. -/
theorem childLoad_of_parts (B : ℕ) (S : Setup L)
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
    -- the channel seam: F7's `htabF (j+1)` is the pass's table
    (hhtab : ∀ (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N),
      htabF (j + 1) (childArena S A ((ord A.N A.G).order) u)
        = chanF j A u)
    (hparts : ChildLoadParts B S ord ℓp htabF hbf Adm Scr ca co cm prepC
      chanF KP) :
    ChildLoad B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP := by
  intro k j A hdiag hAdm hbot u
  refine (hparts k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' - ⟨⟨Dp, Dc, hPT, hAW⟩, hframe⟩
  refine ⟨?_, hframe⟩
  rw [hhtab j A u, ← machChild_eq_ofArena S A ((ord A.N A.G).order) u
    (chanF j A u) hPT]
  exact hAW

/-! ## §5 The headline: `ChildLoadAll` from the parts -/

/-- The parts residual, quantified per admissible input. -/
def ChildLoadPartsAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
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
    ChildLoadParts (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF
      hbf Adm Scr ca co cm prepC chanF KP

open Classical in
/-- **Verbatim `ChildLoadAll`, from the parts** — the prep segment's
machine residual, reduced to the stage composition: what remains for
the discharger is to produce `ChildLoadPartsAll` by composing the five
landed stage lifts with the glue programs, landing at `machChild`'s
five regions; the conversion to `ofArena childArena` is this file's. -/
theorem childLoadAll_of_parts (C : GraphClass) (hC : NowhereDense C)
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
    (hparts : ChildLoadPartsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC chanF KP) :
    ChildLoadAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm prepC
      KP := by
  intro x hx
  exact childLoad_of_parts (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp
    htabF hbf Adm Scr ca co cm prepC chanF KP hhtab (hparts x hx)

/-! ## §6 End to end: verbatim `CentrePrepAll` from the parts -/

open Classical in
/-- **Verbatim `CentrePrepAll`, from the parts** — the whole prep
segment wired through `SolveSegPrep`: the parts residual plus the
descriptor tower's two length-only facts and the channel seam. -/
theorem centrePrepAll_of_parts (C : GraphClass) (hC : NowhereDense C)
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
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
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
    (hparts : ChildLoadPartsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC chanF KP) :
    CentrePrepAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm prepC
      KP :=
  centrePrepAll_of_childLoad C hC φ ord G c w q ℓp htabF hbf Adm Scr
    ca co cm prepC KP hscrLen hscrDown htabLen
    (childLoadAll_of_parts C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC chanF KP hhtab hparts)

end Lax3Proofs.Prog
