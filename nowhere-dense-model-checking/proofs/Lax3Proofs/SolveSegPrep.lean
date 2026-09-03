import Lax3Proofs.SolveStep

/-!
# F6c10a (part 1) — the child construction: the invariant seam, discharged

`SolveStep` reduced the per-centre step to the two straight-line
segments `CentrePrepAll`/`CentreReadAll`. This file discharges the
*invariant seam* of the prep segment — everything `CentrePrep` asserts
beyond what the machine pass itself computes:

* **`ChildLoad`** is the named machine residual: the pass that actually
  builds the child — the cluster-row read (`ClusterCsr.read_row`),
  restrict (`restrictCom_specW`), BFS at `2R` + supports per channel
  round (`bfsCom_specW`/`supportsCom_specW` at `hb = 2R+1`), profilesMS
  at the pre-isolation child (`profilesCom_specW`), isolate
  (`isolateCom_specW`), and the region/color/channel assembly — stated
  at exactly the seam the stage lifts speak: from the loop invariant at
  centre `u` (counter at `u`), it delivers **the windowed contract at
  the level-`(j+1)` names holding the machine child**
  `Impl.ofArena (childArena S A ((ord A.N A.G).order) u) (htabF (j+1) …)`,
  plus its frame data — the level-`j` cells and the level's own
  regions (the counter, the two arena cells, the cover's three arrays,
  the level's six regions) untouched, and no reallocation. The frame
  clauses are what a discharger built from `OwnedFrom`-style freshness
  gets for free off `Run.frame` (`SolveStep`'s `hvarF`/`harrF` shape).
* **`centrePrep_of_childLoad`** discharges the rest of `CentrePrep`
  from that: the loop invariant `CLInv u` crosses the pass by
  `clInv_frame` on the frame clauses alone, the counter clause is the
  frame's, and the inner block's precondition `BlockPre` at the child
  is assembled — the windowed contract is the residual's deliverable
  verbatim, the child's table allocation rides `arenaN_le` (a child
  carrier never outgrows the root) through the level-`(j+1)` table
  length carried by the level-`j` scratch descriptor (`htabLen` —
  length-only, F7's static layout), and the child's scratch descriptor
  `Scr (j+1)` is the descriptor tower's (`hscrDown`, guarded to the
  depths the chain runs) transported by its length-only clause.
* **`centrePrepAll_of_childLoad`** concludes **verbatim
  `CentrePrepAll`** at the same `prepC`/`KP` from `ChildLoadAll`, the
  per-admissible-input quantification of the residual.

No cost is restated: `ChildLoad` carries `KP` itself, so the budget
claim stays the machine discharger's.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The named residual: the child-building machine pass -/

/-- **The child-building machine pass** (named residual): from the loop
invariant at centre `u` with the counter holding `u`, the pass leaves
the level-`(j+1)` regions holding the machine child — the windowed
contract at `Impl.ofArena (childArena S A ((ord A.N A.G).order) u)`
with the chain's own channel table `htabF (j+1)` — and touches nothing
the invariant reads: the level-`j` cells (the counter and the two arena
cells) and the level's own arrays (the cover's three, the six regions)
are untouched, and no array is reallocated. The frame clauses are
exactly what `Run.frame` plus the `lv` freshness facts give a pass that
writes only deeper pools and its own scratch. -/
def ChildLoad (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
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
        (∀ y ∈ ctrName j :: levelScalars j, σ'.vars y = σ.vars y) ∧
        (∀ a ∈ ca j :: co j :: cm j :: levelArrays j, σ'.arrs a = σ.arrs a) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (KP k j A (u : ℕ))

/-! ## §2 `CentrePrep`, from the machine pass -/

open Classical in
/-- **`CentrePrep` from the child-building pass**: the invariant seam
discharged. `CLInv u` crosses the pass by `clInv_frame` on the frame
clauses alone, the counter clause is the frame's, and the child's
`BlockPre` is assembled from the pass's deliverable plus two
length-only facts of the descriptor tower: the level-`(j+1)` table
allocation (`htabLen`, routed below the root carrier by `arenaN_le`)
and the level-`(j+1)` scratch descriptor (`hscrDown` + the length-only
transport), both guarded to the depths the chain actually runs
(`j + 1 ≤ S.depth`, forced by the diagonal). -/
theorem centrePrep_of_childLoad (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (prepC : ℕ → Com)
    (KP : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    -- the length-only scratch transport (the descriptors always are)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    -- the descriptor tower: level `j`'s descriptor carries the deeper
    -- level's, wherever the chain still descends
    (hscrDown : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ → Scr (j + 1) σ)
    -- the level-`(j+1)` table allocation, at the root carrier (the
    -- static layout's; length-only)
    (htabLen : ∀ j, j + 1 ≤ S.depth → ∀ σ, Scr j σ →
      n₀ * (levelFml S (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hload : ChildLoad B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP) :
    CentrePrep B S ord ℓp htabF hbf Adm Scr ca co cm prepC KP := by
  intro k j A hdiag hAdm hbot u
  refine (hload k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' ⟨hCL, -⟩ ⟨hAW, hvars, harrs, hlen⟩
  have hScrj : Scr j σ := hCL.1.2.2
  refine ⟨clInv_frame (hscrLen j) hCL
      (hvars _ (by simp [levelScalars])) (hvars _ (by simp [levelScalars]))
      harrs hlen,
    hvars _ (by simp), hAW, ?_, ?_⟩
  · -- the child's table allocation: below the root carrier, off the
    -- level-`j` descriptor, lengths preserved
    calc (childArena S A ((ord A.N A.G).order) u).N
          * (levelFml S (j + 1)).length
        ≤ n₀ * (levelFml S (j + 1)).length :=
          Nat.mul_le_mul_right _ (arenaN_le _)
      _ ≤ (σ.arrs (arenaNames (j + 1)).tab).length :=
          htabLen j (by omega) σ hScrj
      _ = (σ'.arrs (arenaNames (j + 1)).tab).length := (hlen _).symm
  · -- the child's scratch descriptor: the tower's, transported
    exact hscrLen (j + 1) σ σ' (hscrDown j (by omega) σ hScrj) hlen

/-! ## §3 The headline: `CentrePrepAll` from the pass -/

/-- The child-building pass, quantified per admissible input — at the
word bound of every admissible input. -/
def ChildLoadAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
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
    ChildLoad (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      Adm Scr ca co cm prepC KP

open Classical in
/-- **Verbatim `CentrePrepAll`, from the child-building pass** — the
prep segment's residual, reduced to the machine pass plus the
descriptor tower's two length-only facts. -/
theorem centrePrepAll_of_childLoad (C : GraphClass) (hC : NowhereDense C)
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
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hscrDown : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ σ, Scr j σ → Scr (j + 1) σ)
    (htabLen : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → ∀ σ,
      Scr j σ →
      n * (levelFml (Headline.headlineSetup C hC φ) (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hload : ChildLoadAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      prepC KP) :
    CentrePrepAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm prepC
      KP := by
  intro x hx
  exact centrePrep_of_childLoad (mcB q x) (Headline.headlineSetup C hC φ)
    ord ℓp htabF hbf Adm Scr ca co cm prepC KP hscrLen hscrDown htabLen
    (hload x hx)

end Lax3Proofs.Prog
