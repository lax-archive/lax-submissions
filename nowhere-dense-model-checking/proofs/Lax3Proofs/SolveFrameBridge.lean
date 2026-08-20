import Lax3Proofs.SolveFrameStages

/-!
# F6c7 (part 2) — the closure of `SolveSpec`, at the canonical names

`SolveChain.solveSpec_of_chain` closes `ProgCodegen.SolveSpec` from
four residuals. This file discharges everything *structural* that the
closure still owed — the canonical name family's side conditions and
the bottom block's instantiation — and packages the genuinely open
remainder as three precisely named propositions, so that the final
composition is one theorem, `solveSpec_closed`:

* **`canonBotB`** — the bottom block at the canonical level names
  (`arenaNames j`, the leaf scratch `botNa/botFa/botEa/botXa j`), the
  concrete `botB` the chain runs. §1 discharges every name side
  condition `botBlock_spec` asks (`Nodup`s, freshness against
  `btScalars`) for this family, at every level at once, off the `lv`
  mechanism — nothing is left to F7 here.
* **`FrameStepAll`** — residual 1, quantified the way the closure
  consumes it: `SolveChain.FrameStep` at the word bound of every
  admissible input. Its discharge is the per-centre `Spec.seq` chain
  over the lifted stages (`SolveChainBot`, `SolveChainRestrict`,
  `SolveFrameStages`), the cover slot (`CoverStageSpec`), the glue
  loads, and the leaf branch through `blockSpec_leaf_guard`.
* **`RootLoadSpec`** — residual 3a, verbatim `solveSpec_of_chain`'s
  `hload`: from `MatIn` to the level-0 `BlockPre` at the root arena.
* **`TopScatterAll`** — residual 3b, verbatim `solveSpec_of_chain`'s
  `htop`: `TopScatterSpec` at every admissible input.

**`solveSpec_closed`** then concludes `SolveSpec` outright from these
three named residuals plus the `Adm`-side hypotheses (`hAdmRoot`,
`hdep0` — the run invariant's two facts at the root, F7's) and the
word-size bookkeeping, with the budget assembled by name:
`matK + Krl + KB(depth, 0, root) + Kc + topEvalCost`. Residual 4
(`KsChargeBridge`) is exactly the comparison of this budget against
the charge ledger and stays as `SolveChain` states it — nothing here
changes its shape.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The canonical bottom block, and its name side conditions -/

/-- **The bottom block at the canonical names**: `botCom` over level
`j`'s arena family (`arenaNames j`) and the four leaf scratch regions
of §2 of the head file — the concrete `botB` the chain's static layout
carries at every level. -/
noncomputable def canonBotB (S : Setup L) (Kq : ℕ) (j : ℕ) : Com :=
  botCom (arenaNames j).nN (arenaNames j).col (botNa j) (botFa j) (botEa j)
    (botXa j) (arenaNames j).tab (S.pal j) Kq (levelFml S j)

/-- The six leaf arrays of level `j` are pairwise distinct — the
`hnd` condition, at every level at once. -/
theorem canon_nd (j : ℕ) :
    ([(arenaNames j).col, botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String).Nodup := by
  show ((["sa.c", "sb.n", "sb.f", "sb.e", "sb.x", "sa.b"] : List String).map
    (lv · j)).Nodup
  exact lv_map_nodup (m := 4) (by decide) (by decide) j

/-- The CSR offset name misses the leaf's five — `hoff`. -/
theorem canon_off (j : ℕ) : (arenaNames j).off
    ∉ ([botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab] :
      List String) := by
  show lv "sa.o" j
    ∉ (["sb.n", "sb.f", "sb.e", "sb.x", "sa.b"] : List String).map (lv · j)
  exact lv_notMem_map (m := 4) (by decide) (by decide) (by decide) j j

/-- The CSR target name misses the leaf's five — `htgt`. -/
theorem canon_tgt (j : ℕ) : (arenaNames j).tgt
    ∉ ([botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab] :
      List String) := by
  show lv "sa.t" j
    ∉ (["sb.n", "sb.f", "sb.e", "sb.x", "sa.b"] : List String).map (lv · j)
  exact lv_notMem_map (m := 4) (by decide) (by decide) (by decide) j j

/-- The renaming name misses the leaf's five — `hup`. -/
theorem canon_up (j : ℕ) : (arenaNames j).up
    ∉ ([botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab] :
      List String) := by
  show lv "sa.u" j
    ∉ (["sb.n", "sb.f", "sb.e", "sb.x", "sa.b"] : List String).map (lv · j)
  exact lv_notMem_map (m := 4) (by decide) (by decide) (by decide) j j

/-- The channel name misses the leaf's five — `hhist`. -/
theorem canon_hist (j : ℕ) : (arenaNames j).hist
    ∉ ([botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab] :
      List String) := by
  show lv "sa.h" j
    ∉ (["sb.n", "sb.f", "sb.e", "sb.x", "sa.b"] : List String).map (lv · j)
  exact lv_notMem_map (m := 4) (by decide) (by decide) (by decide) j j

/-- The carrier cell is fresh against the leaf's scratch scalars —
`hnN`. -/
theorem canon_nN (j : ℕ) : (arenaNames j).nN ∉ btScalars :=
  lv_not_mem (by decide) (by decide) j

/-- The slot-count cell is fresh against the leaf's scratch scalars —
`hnS`. -/
theorem canon_nS (j : ℕ) : (arenaNames j).nS ∉ btScalars :=
  lv_not_mem (by decide) (by decide) j

/-- The five region names of one level are pairwise distinct —
`hnd5`. -/
theorem canon_nd5 (j : ℕ) :
    ([(arenaNames j).off, (arenaNames j).tgt, (arenaNames j).col,
      (arenaNames j).up, (arenaNames j).hist] : List String).Nodup := by
  show ((["sa.o", "sa.t", "sa.c", "sa.u", "sa.h"] : List String).map
    (lv · j)).Nodup
  exact lv_map_nodup (m := 4) (by decide) (by decide) j

/-! ## §2 The three named residuals, at the closure's quantifiers -/

/-- **Residual 1, quantified for the closure**: the frame step at the
word bound of every admissible input — `SolveChain.FrameStep`'s
statement, nothing weakened. Its discharge composes the lifted stages
(`SolveChainBot`/`SolveChainRestrict`/`SolveFrameStages`), the cover
slot (`CoverStageSpec`), the per-centre glue and the leaf branch
(`blockSpec_leaf_guard`). -/
def FrameStepAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (frameBody : ℕ → Com → Com) : Prop :=
  ∀ x ∈ mcD n G c w,
    FrameStep (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      arenaNames Adm KB Scr LS LA frameBody

/-- **Residual 3a, named**: the root load — from the materialized root
(`MatIn`) to the level-0 `BlockPre` at the root arena, verbatim
`solveSpec_of_chain`'s `hload`. Its discharge is a CSR copy into the
level-0 names plus the two cells (`topCom_spec`'s sibling seam). -/
def RootLoadSpec (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ)
    (ext : List ℕ → String → ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Scr : ℕ → Env → Prop) (rootLoadCom : Com)
    (Krl : List ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    Spec (mcB q x) (MatIn (ext x) x) rootLoadCom
      (fun _ σ' => BlockPre (Headline.headlineSetup C hC φ) 0 (hbf 0)
        (rootArena G (Impl.trivialColoring n))
        (htabF 0 (rootArena G (Impl.trivialColoring n))) (Scr 0)
        (arenaNames 0) σ')
      (Krl x)

/-- **Residual 3b, named**: the top scatter — `TopScatterSpec` at every
admissible input, from the root block's postcondition *plus the top
stage's length-only scratch descriptor* `Scr` (the closure instantiates
it at the level-0 descriptor `Scr 0`, which the root load establishes
and the chain preserves — `TopScatterSpec`'s docstring), verbatim
`solveSpec_of_chain`'s `htop`. -/
def TopScatterAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Scr : Env → Prop) (scatCom : Com)
    (av : ScatterSentence 0 → Expr) (Kc : ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    TopScatterSpec (mcB q x) (Headline.headlineSetup C hC φ) ord G
      (Impl.trivialColoring n)
      (BlockPost (Headline.headlineSetup C hC φ) ord
        (Headline.headlineSetup C hC φ).depth 0 (hbf 0)
        (rootArena G (Impl.trivialColoring n))
        (htabF 0 (rootArena G (Impl.trivialColoring n))) (arenaNames 0))
      Scr scatCom av Kc

/-! ## §3 The closure -/

open Classical in
/-- **`SolveSpec`, closed at the canonical names** — the leaf's
composition theorem. From the three named residuals (`FrameStepAll`,
`RootLoadSpec`, `TopScatterAll`), the `Adm`-side facts at the root
(`hAdmRoot`, `hdep0` — F7's run invariant), and the word-size and
layout bookkeeping (the `< B` bounds at the bottom level, the leaf
budget's fit into `KB`, the scratch descriptor's lengths, the name
pools), the solve pipeline

`matCom ; rootLoadCom ; chainCom(frameBody, canonBotB) ; topCom`

satisfies `ProgCodegen.SolveSpec` at the named budget
`matK + Krl + KB(depth, 0, root) + Kc + topEvalCost`. The bottom
block is `canonBotB` — its `BlockSpec` is discharged here through
`botBlock_spec` with every name condition supplied by §1; the level
chain is `chainCom_blockSpec`; the closure is `solveSpec_of_chain`. -/
theorem solveSpec_closed
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ext : List ℕ → String → ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (frameBody : ℕ → Com → Com)
    (rootLoadCom scatCom : Com) (av : ScatterSentence 0 → Expr)
    (Krl : List ℕ → ℕ) (Kc Kq : ℕ)
    -- the schedule's `q` and the parse convention
    (hq : 1 ≤ q)
    (hextUp : ∀ x ∈ mcD n G c w, ext x "up" = vertexCount x)
    -- the run invariant's two facts at the root (F7's)
    (hAdmRoot : Adm 0 (rootArena G (Impl.trivialColoring n)))
    (hdep0 : (Headline.headlineSetup C hC φ).depth = 0 → G = ⊥)
    -- the level-0 scratch descriptor is length-only, so it crosses the
    -- chain to the top scatter stage (`TopScatterSpec`'s docstring)
    (hscrLen0 : ∀ σ σ', Scr 0 σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr 0 σ')
    -- the bottom level's schedule-rank and word-size bookkeeping
    (hKq : ∀ β ∈ levelFml (Headline.headlineSetup C hC φ)
      (Headline.headlineSetup C hC φ).depth, qdepth β ≤ Kq)
    (hB : ∀ x ∈ mcD n G c w,
      n < mcB q x ∧
      n * (Headline.headlineSetup C hC φ).pal
        (Headline.headlineSetup C hC φ).depth < mcB q x ∧
      2 ^ (Headline.headlineSetup C hC φ).pal
        (Headline.headlineSetup C hC φ).depth * (Kq + 1) < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ)
        (Headline.headlineSetup C hC φ).depth).length < mcB q x)
    -- the bottom level's scratch descriptor and budget fit
    (hscr : ∀ σ, Scr (Headline.headlineSetup C hC φ).depth σ →
      (σ.arrs (botNa (Headline.headlineSetup C hC φ).depth)).length
        = 2 ^ (Headline.headlineSetup C hC φ).pal
            (Headline.headlineSetup C hC φ).depth ∧
      (σ.arrs (botFa (Headline.headlineSetup C hC φ).depth)).length
        = 2 ^ (Headline.headlineSetup C hC φ).pal
            (Headline.headlineSetup C hC φ).depth * (Kq + 1) ∧
      (σ.arrs (botEa (Headline.headlineSetup C hC φ).depth)).length
        = Kq + 1 ∧
      (σ.arrs (botXa (Headline.headlineSetup C hC φ).depth)).length
        = Kq + 1)
    (hKB0 : ∀ A : Arena ((Headline.headlineSetup C hC φ).pal
        (Headline.headlineSetup C hC φ).depth) n,
      botComK A.N ((Headline.headlineSetup C hC φ).pal
          (Headline.headlineSetup C hC φ).depth) Kq
          (levelFml (Headline.headlineSetup C hC φ)
            (Headline.headlineSetup C hC φ).depth)
        ≤ KB 0 (Headline.headlineSetup C hC φ).depth A)
    -- the name pools carry the leaf's names
    (hLS : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ j, ∀ a ∈ ([botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String), a ∈ LA j)
    -- the three named residuals
    (hstep : FrameStepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      frameBody)
    (hload : RootLoadSpec C hC φ G c w q ext ℓp htabF hbf Scr rootLoadCom Krl)
    (htop : TopScatterAll C hC φ ord G c w q ℓp htabF hbf (Scr 0) scatCom
      av Kc) :
    SolveSpec C hC φ ord G c w q ext
      (.seq matCom
        (.seq rootLoadCom
          (.seq (chainCom frameBody (canonBotB (Headline.headlineSetup C hC φ) Kq)
              (Headline.headlineSetup C hC φ).depth 0)
            (topCom scatCom (Headline.headlineSetup C hC φ) av))))
      (fun x => matK x + (Krl x +
        (KB (Headline.headlineSetup C hC φ).depth 0
            (rootArena G (Impl.trivialColoring n)) +
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))) := by
  refine solveSpec_of_chain C hC φ ord G c w q ext ℓp htabF hbf arenaNames
    Adm KB Scr frameBody (canonBotB (Headline.headlineSetup C hC φ) Kq)
    rootLoadCom scatCom av Krl Kc hq hextUp hAdmRoot hdep0 hscrLen0 ?_
    hload htop
  -- the chain's contract at the root, from the canonical bottom block
  -- and the frame-step residual
  intro x hx
  obtain ⟨hn0B, hNLB, h2LB, hTB⟩ := hB x hx
  have hbot : ∀ j, BlockSpec (mcB q x) (Headline.headlineSetup C hC φ) ord
      ℓp htabF hbf arenaNames Adm KB Scr 0 j
      (canonBotB (Headline.headlineSetup C hC φ) Kq j) ∧
      OwnedFrom LS LA j (canonBotB (Headline.headlineSetup C hC φ) Kq j) := by
    intro j
    refine ⟨?_, botBlock_owned LS LA arenaNames j Kq _ (hLS j) (hLA j)⟩
    by_cases hj : j = (Headline.headlineSetup C hC φ).depth
    · subst hj
      exact botBlock_spec (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp
        htabF hbf arenaNames Adm KB Scr _ Kq hKq hn0B hNLB h2LB hTB
        (canon_nd _) (canon_off _) (canon_tgt _) (canon_up _) (canon_hist _)
        (canon_nN _) (canon_nS _) (canon_nd5 _) hscr hKB0
    · -- off the bottom of the diagonal the contract is vacuous: fuel
      -- `0` forces `j = depth`
      intro A hdiag _ _
      exact absurd (by omega : j = (Headline.headlineSetup C hC φ).depth) hj
  exact (chainCom_blockSpec (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp
    htabF hbf arenaNames Adm KB Scr LS LA frameBody
    (canonBotB (Headline.headlineSetup C hC φ) Kq) hbot (hstep x hx)
    (Headline.headlineSetup C hC φ).depth 0).1

end Lax3Proofs.Prog
