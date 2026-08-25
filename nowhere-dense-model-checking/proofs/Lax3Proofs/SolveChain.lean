import Lax3Proofs.SolveMat
import Lax3Proofs.SolveChainBot
import Lax3Proofs.SolveChainCover
import Lax3Proofs.ProgDriver
import Lax3Proofs.ProgCharge
import Lax3Proofs.SolveBlocksRestrict
import Lax3Proofs.SolveBlocksSupports
import Lax3Proofs.SolveBlocksProfiles

/-!
# F6c6 — the frame chain: `ℓ+1` levels closing `SolveSpec`, conditionally

The composition leaf. Everything below `SolveSpec` is landed: the six
stage programs with their `Spec`s (`restrictCom`/`isolateCom`,
`bfsCom`, `supportsCom`, `profilesCom`, `botCom`, `scatterCom`), the
two bookends (`matCom`, `topCom`), the NREST mirror the chain must
shadow (`ProgDriver.driverProg_le_spec` — `ℓ+1` static blocks by
recursion on the level index), and — from this wave — the windowed
contract and its generic transport (`SolveChainWin`), the leaf stage
lifted through it (`SolveChainBot`), and the cover stage's machine
interface (`SolveChainCover`).

This file is the chain's **structure**: the per-level block contract
(`BlockSpec` — the machine mirror of `driverProg_le_spec`'s per-level
statement), the static layout (`chainCom` — block `j` contains one
copy of block `j+1`, exactly `Unroll`'s layout paragraph), the level
induction (`chainCom_blockSpec` — `driverProg_le_spec`'s induction at
the `Spec` layer), the discharged bottom block (`botBlock_spec`, off
the lifted leaf stage), and the closure of `ProgCodegen.SolveSpec`
(`solveSpec_of_chain`) through `solveSpec_of_rest` and `topCom_spec`,
with the budget `Ks` assembled by name from the landed per-stage
budgets (`centreK`/`frameK`) and the bridge to the charge ledger
stated as the named obligation `KsChargeBridge`.

## The contract, and why it is stated the way it is

`BlockSpec B S ord … k j com`: *for every admissible depth-`j` arena
on the diagonal `j + k = S.depth`, from the level's windowed regions
holding the arena (`BlockPre`), `com` leaves the regions intact and
the level's table region holding `Unroll.unrollAux S ord k j A` at the
schedule family `ℱ_j` (`BlockPost`), within `KB k j A`.*

* **The diagonal.** The machine only ever runs fuel `ℓ − j` at depth
  `j`; off the diagonal the fuel-`0` edgeless guard would be
  undischargeable (`Unroll.memLeaf_eq_bot` is a statement about depth
  `ℓ`). `driverProg_le_spec` can afford all `(k, j)` because its
  bottom block returns the abstract value on edged arenas — dead code
  a machine cannot compile (`ProgDriver`'s hazard note). Restricting
  to the diagonal is the machine-side resolution: block `0`'s `Spec`
  carries the edgeless hypothesis, and the run invariant
  (`mkSetup_memLeaf_eq_bot`, through `Adm`) supplies it exactly where
  the chain calls it.
* **`Adm` is abstract.** The chain needs only that the instantiator
  can maintain admissibility down the recursion; the campaign's
  concrete instance is membership in the run tree (`Unroll` half 2),
  whose closure properties are landed. Threading the concrete tree
  here would force this file to re-state F7's setup hypotheses.
* **`Scr` is abstract; it is *not* length-only.** Each level's
  scratch *allocations* (the leaf's four regions, the cover outputs,
  the profile tables, …) are lengths fixed by the static layout, and
  those do survive every stage for free by `specArrsLength`. But the
  descriptor also has to carry the child-building pass's one
  **content** clause — the clean rank scratch `RankScr` — and
  `SolveMachPrepSeam.rankScr_not_length_only` shows that a descriptor
  implying `RankScr` and admitting the length-only `∀ σ σ'` transport
  is inconsistent. §3b names the two transports such a descriptor
  really has (`ScrFrame`, `ScrStep`) and §5–§6 carry it with those:
  `BlockPostScr`/`BlockSpecScr` conjoin `Scr j` to the block's
  postcondition, so the descriptor crosses `chainCom` because each
  block *restores* it, not because lengths are preserved.
* **`OwnedFrom` is the name discipline**: block `j` writes only names
  belonging to levels `≥ j` (the `lv` mechanism keeps the families
  apart — `arenaNames_arrays_ne_of_level_ne`). It is what lets the
  frame-step discharger carry the *parent's* regions across the inner
  block by `Spec.frame` alone.

## The two named obligations this file leaves (the continuation map)

1. **`FrameStep`** — one non-leaf block's body: given block `j+1`'s
   `BlockSpec`, build block `j`'s. Its discharge is the per-centre
   `Spec.seq` chain (cover-read → `restrictCom` → `bfsCom` +
   `supportsCom` → `profilesCom` → `isolateCom` → the inner block →
   `scatterCom` per atom → readback), the centre loop, and the leaf
   branch through the *discharged* `botBlock_spec` behind the `nS = 0`
   guard (`GraphCsr.ns_eq_sum_degree`: slot count zero **is**
   edgelessness). The landed stage `Spec`s enter through `specWindow`
   exactly as `SolveChainBot` demonstrates; the cover slot enters
   through `CoverStageSpec`; the glue (region loads, the batch
   assembly from the channel, the per-centre count region, the
   readback's `bcExpr` evaluation per schedule row) is new IMP+ in
   `ProgCodegenParse`'s style.
2. **`CoverStageSpec`** (per level/arena, `SolveChainCover`) — the GKS
   sweep against `Impl.sweepCluster_eq_cluster`/`sweepCtr_eq_centre`.

Plus the two seam residuals of the `SolveSpec` closure: the root load
(`MatIn` → level-0 `BlockPre` at the root arena — a CSR copy into the
level-0 names plus the two cells) and the top scatter stage
(`TopScatterSpec` — the per-atom guarded counts over the root table
into `verdictCom`'s read expressions, `scatterCom_spec_graphCsr` per
atom plus a column extraction). Both are `Spec`-shaped hypotheses of
`solveSpec_of_chain`, quantified per admissible input.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun
open Lax13Proofs.Refine (ACost)

variable {L n₀ : ℕ}

/-! ## §1 The level's schedule family, as the table region's index list -/

/-- **The level's schedule family `ℱ_j`, as a list of raw formulas** —
the index list of the level's `TableBits` region (the head file's
contract states the table at it). -/
noncomputable def levelFml (S : Setup L) (j : ℕ) : List (DistFO (S.pal j) 1) :=
  (F S j).map Fml.fml

theorem levelFml_length (S : Setup L) (j : ℕ) :
    (levelFml S j).length = (F S j).length := List.length_map ..

theorem mem_levelFml {S : Setup L} {j : ℕ} {β : DistFO (S.pal j) 1} :
    β ∈ levelFml S j ↔ ∃ γ ∈ F S j, γ.fml = β := List.mem_map

/-- Every schedule-family entry is local of rank `(1, q−1)` — the rank
invariant, at the raw list. -/
theorem levelFml_rank (S : Setup L) (j : ℕ) :
    ∀ β ∈ levelFml S j, IsLocal β ∧ DRank 1 (S.q - 1) β := by
  intro β hβ
  obtain ⟨γ, -, rfl⟩ := mem_levelFml.mp hβ
  exact ⟨γ.isLocal, γ.drank⟩

/-- The `β`-formula of every scatter atom of `top` is a root
schedule-family entry — how the top scatter stage's columns index into
the root table region. -/
theorem beta_mem_levelFml_zero (S : Setup L) {σa : ScatterSentence L}
    (h : σa ∈ scatterAtoms S.choice S.φ S.hφ) : σa.β ∈ levelFml S 0 := by
  obtain ⟨γ, hγ, hfml⟩ := exists_mem_F_zero_of_scatterAtom S h
  exact mem_levelFml.mpr ⟨γ, hγ, hfml⟩

/-! ## §2 Name plumbing: the `lv` mechanism, packaged for consumers -/

/-- A level-tagged name misses any list its base misses, provided the
list's entries all have the base's length — how `∉ btScalars`-style
side conditions are discharged at every level at once. -/
theorem lv_not_mem {s : String} {l : List String} (hs : s ∉ l)
    (hlen : ∀ t ∈ l, t.length = s.length) (j : ℕ) : lv s j ∉ l := by
  intro hmem
  have h1 := hlen _ hmem
  rw [lv_length] at h1
  have hj : j = 0 := by omega
  subst hj
  exact hs hmem

/-- Tagging a `Nodup` family of same-length bases stays `Nodup` at
every level. -/
theorem lv_map_nodup {bs : List String} {m : ℕ} (h4 : ∀ s ∈ bs, s.length = m)
    (hnd : bs.Nodup) (j : ℕ) : (bs.map (lv · j)).Nodup := by
  refine List.Nodup.map_on ?_ hnd
  intro s hs t ht h
  exact (lv_inj (by rw [h4 s hs, h4 t ht]) h).1

/-- A tagged name of a fresh base misses the tagged family of any base
list not containing it (all of one length, any two levels). -/
theorem lv_notMem_map {s : String} {bs : List String} {m : ℕ}
    (h4s : s.length = m) (h4 : ∀ t ∈ bs, t.length = m) (hs : s ∉ bs)
    (j k : ℕ) : lv s j ∉ bs.map (lv · k) := by
  intro hmem
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hmem
  obtain ⟨rfl, -⟩ := lv_inj (by rw [h4 t ht, h4s]) heq
  exact hs ht

/-- The canonical leaf-stage scratch names of level `j` (bases of
length 4, per the `lv_inj` requirement; fresh against `arenaBases`). -/
def botNa (j : ℕ) : String := lv "sb.n" j
/-- Leaf scratch: the packed row-code region. -/
def botFa (j : ℕ) : String := lv "sb.f" j
/-- Leaf scratch: the evaluator's environment region. -/
def botEa (j : ℕ) : String := lv "sb.e" j
/-- Leaf scratch: the evaluator's mark region. -/
def botXa (j : ℕ) : String := lv "sb.x" j

/-! ## §3 The per-level block contract -/

/-- **What a block starts from**: the level's windowed regions holding
the arena (the machine arena is the driver's, with the channel table
`htab` — `ProgDriver`'s free parameter), a table allocation of at least
`A.N·|ℱ_j|` cells, and the level's scratch descriptor (abstract,
length-only — module docstring). -/
def BlockPre (S : Setup L) (j : ℕ) {ℓpj : ℕ} (hbj : ℕ)
    (A : Arena (S.pal j) n₀) (htab : Fin A.N → Fin ℓpj → List (Fin A.N))
    (Scr : Env → Prop) (nm : ArenaNames) (σ : Env) : Prop :=
  ArenaStW nm hbj (Impl.ofArena A htab) σ ∧
    A.N * (levelFml S j).length ≤ (σ.arrs nm.tab).length ∧ Scr σ

/-- **What a block leaves**: the regions intact, and the level's table
region holding exactly `Unroll.unrollAux`'s values at the schedule
family — the machine mirror of `driverProg_le_spec`'s postcondition. -/
def BlockPost (S : Setup L) (ord : CoverSpec.OrderingRoutine) (k j : ℕ)
    {ℓpj : ℕ} (hbj : ℕ) (A : Arena (S.pal j) n₀)
    (htab : Fin A.N → Fin ℓpj → List (Fin A.N)) (nm : ArenaNames)
    (σ' : Env) : Prop :=
  ArenaStW nm hbj (Impl.ofArena A htab) σ' ∧
    TableBitsW nm.tab (levelFml S j) (Unroll.unrollAux S ord k j A) σ'

/-- **The per-level block contract** — `driverProg_le_spec`'s per-level
statement at the `Spec` layer, on the diagonal `j + k = S.depth` (the
only fuel the machine runs; module docstring), over every admissible
arena, with the fuel-`0` edgeless guard explicit. -/
def BlockSpec (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (k j : ℕ) (com : Com) : Prop :=
  ∀ A : Arena (S.pal j) n₀, j + k = S.depth → Adm j A → (k = 0 → A.G = ⊥) →
    Spec B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j)) com
      (fun _ σ' => BlockPost S ord k j (hbf j) A (htabF j A) (nmF j) σ')
      (KB k j A)

/-- **What a block leaves, with the level's descriptor standing** —
verbatim `BlockPost` plus the conjunct `Scr σ'`.

`BlockPost` carries no `Scr` conjunct, so nothing about the descriptor
survives `chainCom` on its own; `solveSpec_of_chain` bridges that gap
by the only route open to it, converting length preservation back into
`Scr 0` — the route `rankScr_not_length_only` refutes for a descriptor
that carries content. Conjoining the descriptor to the postcondition is
the additive repair, the same move `SolveMachPrepSeam`'s `ChildLoadScr`
makes for the child-building pass, and it is a claim a block can make:
its own child-building pass restores the scratch it uses, and nothing
else in the block touches the level's scratch. -/
def BlockPostScr (S : Setup L) (ord : CoverSpec.OrderingRoutine) (k j : ℕ)
    {ℓpj : ℕ} (hbj : ℕ) (A : Arena (S.pal j) n₀)
    (htab : Fin A.N → Fin ℓpj → List (Fin A.N)) (Scr : Env → Prop)
    (nm : ArenaNames) (σ' : Env) : Prop :=
  BlockPost S ord k j hbj A htab nm σ' ∧ Scr σ'

/-- **The per-level block contract, with the descriptor restored** —
verbatim `BlockSpec` at the strengthened postcondition. -/
def BlockSpecScr (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (k j : ℕ) (com : Com) : Prop :=
  ∀ A : Arena (S.pal j) n₀, j + k = S.depth → Adm j A → (k = 0 → A.G = ⊥) →
    Spec B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j)) com
      (fun _ σ' => BlockPostScr S ord k j (hbf j) A (htabF j A) (Scr j)
        (nmF j) σ')
      (KB k j A)

/-- The strengthened contract weakens back to the landed one: nothing
that consumes `BlockSpec` is deprived. -/
theorem blockSpec_of_blockSpecScr (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    {htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)}
    {hbf : ℕ → ℕ} {nmF : ℕ → ArenaNames}
    {Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop}
    {KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ} {Scr : ℕ → Env → Prop}
    {k j : ℕ} {com : Com}
    (h : BlockSpecScr B S ord ℓp htabF hbf nmF Adm KB Scr k j com) :
    BlockSpec B S ord ℓp htabF hbf nmF Adm KB Scr k j com := fun A hd hA h0 =>
  (h A hd hA h0).post (fun _ _ _ hq => hq.1)

/-- **The write discipline**: every name a block writes belongs to its
own level or deeper — what lets a frame carry the parent's regions
across the inner block by `Spec.frame` alone. The per-level name pools
`LS`/`LA` are the instantiator's (they include the level's region
names, its scratch, and the shared stage scratch). -/
def OwnedFrom (LS LA : ℕ → List String) (j : ℕ) (c : Com) : Prop :=
  (∀ y ∈ c.wvars, ∃ i, j ≤ i ∧ y ∈ LS i) ∧
  (∀ a ∈ c.warrs, ∃ i, j ≤ i ∧ a ∈ LA i)

/-! ## §3b The scratch descriptor's honest transports

The head file's claim that `Scr` is "abstract **and length-only**" is
refuted by `SolveMachPrepSeam.rankScr_not_length_only`: a descriptor
that implies the clean-rank-scratch clause `RankScr` and satisfies the
length-only `∀ σ σ'` transport is *inconsistent* at any state with a
non-empty window — flipping one cell of the scratch preserves every
length. The clean scratch is the one **content** clause the
child-building pass needs from the loop invariant, so the descriptor
must carry content and the transport must change.

The two shapes below are what a content-carrying descriptor can
actually meet. Both name the descriptor's own **read pool** — the
per-level scalar cells `LV j` and arrays `LR j` it looks at — instead
of quantifying over lengths:

* **`ScrFrame`** is `rankScr_frame`'s shape, level by level: `Scr j`
  survives any step that leaves the read pool of level `j` *and of
  every deeper level* alone and reallocates nothing. Every stage that
  does not run the inner block has this — the counter bump, the cover
  stage, the return path, the leaf block.
* **`ScrStep`** is what the inner block has instead. The block
  rewrites level `(j+1)`'s scratch (its own child-building pass does),
  so no frame reaches the deeper half of `Scr j`; what the block
  *does* deliver is `Scr (j+1)` at its exit (`BlockPostScr`), and
  `ScrStep` says level `j`'s descriptor is that plus level `j`'s own
  read pool, framed.

Neither is satisfied only by a length-only descriptor: §7 of
`SolveScrFrameSat` exhibits a `RankScr`-carrying `Scr` meeting both,
together with the descriptor tower `hscrDown` the prep segment asks
for. -/

/-- **Agreement on the level-`j` descriptor's read pool** — its own
cells and arrays and every deeper level's, since the descriptor tower
makes `Scr j` speak about levels `≥ j`. -/
def ScrAgree (LV LR : ℕ → List String) (j : ℕ) (σ σ' : Env) : Prop :=
  (∀ i, j ≤ i → ∀ y ∈ LV i, σ'.vars y = σ.vars y) ∧
  (∀ i, j ≤ i → ∀ a ∈ LR i, σ'.arrs a = σ.arrs a)

/-- **A command that writes nothing the level-`j` descriptor reads** —
the syntactic side condition that turns any `Spec` into a transport of
`Scr j` (`specScr`). Read off `Com.wvars`/`Com.warrs` at the call
site, exactly like `OwnedFrom`. -/
def ScrFree (LV LR : ℕ → List String) (j : ℕ) (c : Com) : Prop :=
  (∀ i, j ≤ i → ∀ y ∈ LV i, y ∉ c.wvars) ∧
  (∀ i, j ≤ i → ∀ a ∈ LR i, a ∉ c.warrs)

/-- **The descriptor's frame transport**: `Scr j` crosses any step that
agrees on its read pool and reallocates nothing. This is
`SolveMachPrepSeam.rankScr_frame`'s shape (array and cell agreement,
*not* lengths), lifted to the whole level-indexed descriptor. -/
def ScrFrame (Scr : ℕ → Env → Prop) (LV LR : ℕ → List String) : Prop :=
  ∀ (j : ℕ) (σ σ' : Env), Scr j σ → ScrAgree LV LR j σ σ' →
    (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ'

/-- **The descriptor's transport across a block**: level `j`'s
descriptor is re-established from the one the block restores at level
`j + 1` (`BlockPostScr`) together with level `j`'s **own** read pool,
framed. This is the transport the inner block has and `ScrFrame` does
not: a block rewrites the deeper scratch and gives it back only as a
descriptor, never as an array equality. -/
def ScrStep (Scr : ℕ → Env → Prop) (LV LR : ℕ → List String) : Prop :=
  ∀ (j : ℕ) (σ σ' : Env), Scr j σ → Scr (j + 1) σ' →
    (∀ y ∈ LV j, σ'.vars y = σ.vars y) →
    (∀ a ∈ LR j, σ'.arrs a = σ.arrs a) →
    (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ'

/-- **Free strengthening of any `Spec` by the descriptor's transport** —
the analogue of `specArrsLength` for a descriptor that carries content:
a command that writes no name the level-`j` descriptor reads carries
`Scr j` across, and the length preservation comes along as before. -/
theorem specScr {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    {Scr : ℕ → Env → Prop} {LV LR : ℕ → List String} {j : ℕ}
    (hfr : ScrFrame Scr LV LR) (hfree : ScrFree LV LR j c)
    (h : Spec B P c Q K) :
    Spec B P c
      (fun σ σ' => Q σ σ' ∧ (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (Scr j σ → Scr j σ')) K := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ
  refine ⟨σ', hr, hq, run_arrs_length_eq hr, fun hs => hfr j σ σ' hs
    ⟨fun i hi y hy => hr.frame_var y (hfree.1 i hi y hy),
      fun i hi a ha => hr.frame_arr a (hfree.2 i hi a ha)⟩
    (run_arrs_length_eq hr)⟩

/-- The read pool is untouched by an assignment to a cell outside it —
the counter bump's transport, and the only `ScrAgree` a call site ever
builds by hand. -/
theorem ScrAgree.setVar {LV LR : ℕ → List String} {j : ℕ} {x : String}
    {σ : Env} {v : ℕ} (hx : ∀ i, j ≤ i → x ∉ LV i) :
    ScrAgree LV LR j σ (σ.setVar x v) :=
  ⟨fun i hi y hy => by
      have hne : y ≠ x := fun h => hx i hi (h ▸ hy)
      simp [hne], fun _ _ _ _ => rfl⟩

/-! ## §4 The static layout, and the level induction -/

/-- **The `ℓ+1` static blocks** (`Unroll`'s layout paragraph, E10):
block at fuel `k+1`, depth `j` is the frame body wrapped around the
one static copy of the block at fuel `k`, depth `j+1`; fuel `0` is the
leaf block. The recursion is on the fuel index only — no block
contains itself. -/
def chainCom (frameBody : ℕ → Com → Com) (botB : ℕ → Com) : ℕ → ℕ → Com
  | 0, j => botB j
  | k + 1, j => frameBody j (chainCom frameBody botB k (j + 1))

/-- **The frame-step obligation** (named residual 1, the continuation
map's bulk): one non-leaf block's body — given the inner block's
contract and write discipline, the frame body around it satisfies the
level's contract and discipline. Its discharge is the per-centre
`Spec.seq` chain over the landed stage `Spec`s (module docstring). -/
def FrameStep (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (frameBody : ℕ → Com → Com) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpec B S ord ℓp htabF hbf nmF Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    BlockSpec B S ord ℓp htabF hbf nmF Adm KB Scr (k + 1) j
        (frameBody j nxCom) ∧
      OwnedFrom LS LA j (frameBody j nxCom)

/-- **The frame-step obligation, with the descriptor restored** —
verbatim `FrameStep` at the strengthened contract on both sides: the
body may *use* the inner block's restored descriptor (`ScrStep` is what
carries the parent's across the recursion window) and must restore its
own level's. -/
def FrameStepScr (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (frameBody : ℕ → Com → Com) : Prop :=
  ∀ (k j : ℕ) (nxCom : Com),
    BlockSpecScr B S ord ℓp htabF hbf nmF Adm KB Scr k (j + 1) nxCom →
    OwnedFrom LS LA (j + 1) nxCom →
    BlockSpecScr B S ord ℓp htabF hbf nmF Adm KB Scr (k + 1) j
        (frameBody j nxCom) ∧
      OwnedFrom LS LA j (frameBody j nxCom)

/-- **The level chain** — `driverProg_le_spec`'s induction at the
`Spec` layer: from the leaf block's contract at every depth and the
frame-step obligation, every block of the static layout satisfies its
level's contract. The chain itself is unconditional plumbing; the
content lives in the two hypotheses. -/
theorem chainCom_blockSpec (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (frameBody : ℕ → Com → Com) (botB : ℕ → Com)
    (hbot : ∀ j, BlockSpec B S ord ℓp htabF hbf nmF Adm KB Scr 0 j (botB j) ∧
      OwnedFrom LS LA j (botB j))
    (hstep : FrameStep B S ord ℓp htabF hbf nmF Adm KB Scr LS LA frameBody) :
    ∀ k j, BlockSpec B S ord ℓp htabF hbf nmF Adm KB Scr k j
        (chainCom frameBody botB k j) ∧
      OwnedFrom LS LA j (chainCom frameBody botB k j) := by
  intro k
  induction k with
  | zero => exact hbot
  | succ k ih =>
    intro j
    obtain ⟨h1, h2⟩ := ih (j + 1)
    exact hstep k j _ h1 h2

/-- **The level chain, with the descriptor restored** — the same
induction at the strengthened contract. -/
theorem chainCom_blockSpecScr (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
    (LS LA : ℕ → List String) (frameBody : ℕ → Com → Com) (botB : ℕ → Com)
    (hbot : ∀ j, BlockSpecScr B S ord ℓp htabF hbf nmF Adm KB Scr 0 j
        (botB j) ∧
      OwnedFrom LS LA j (botB j))
    (hstep : FrameStepScr B S ord ℓp htabF hbf nmF Adm KB Scr LS LA
      frameBody) :
    ∀ k j, BlockSpecScr B S ord ℓp htabF hbf nmF Adm KB Scr k j
        (chainCom frameBody botB k j) ∧
      OwnedFrom LS LA j (chainCom frameBody botB k j) := by
  intro k
  induction k with
  | zero => exact hbot
  | succ k ih =>
    intro j
    obtain ⟨h1, h2⟩ := ih (j + 1)
    exact hstep k j _ h1 h2

/-! ## §5 The bottom block, discharged -/

/-- Carriers never outgrow the root (the driver arena's own renaming
embeds it). -/
theorem arenaN_le {Λ : ℕ} (A : Arena Λ n₀) : A.N ≤ n₀ := by
  have := Fintype.card_le_of_embedding A.up
  simpa using this

/-- `Unroll.unrollAux` at an edgeless arena is satisfaction at the
arena, at **every** fuel — the fuel-`0` clause is `botFrame` and the
recursive clause's leaf branch returns the same table. This is what
lets one compiled leaf block serve both the fuel-`0` bottom and every
level's edgeless guard. -/
theorem unrollAux_of_bot (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {k j : ℕ} (A : Arena (S.pal j) n₀) (hbot : A.G = ⊥) :
    Unroll.unrollAux S ord k j A
      = fun (v : Fin A.N) (β : DistFO (S.pal j) 1) =>
          Sat A.G A.col (fun _ => v) β := by
  cases k with
  | zero => rfl
  | succ k => rw [Unroll.unrollAux, Unroll.frameEval, if_pos hbot]

section BotBlock

variable (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
  (ℓp : ℕ → ℕ)
  (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
    Fin A.N → Fin (ℓp j) → List (Fin A.N))
  (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
  (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
  (KB : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) (Scr : ℕ → Env → Prop)
  (j Kq : ℕ) {na fa ea xa : String}

variable
  (hq : ∀ β ∈ levelFml S j, qdepth β ≤ Kq)
  (hn0B : n₀ < B) (hNLB : n₀ * S.pal j < B)
  (h2LB : 2 ^ S.pal j * (Kq + 1) < B)
  (hTB : n₀ * (levelFml S j).length < B)
  (hnd : [(nmF j).col, na, fa, ea, xa, (nmF j).tab].Nodup)
  (hoff : (nmF j).off ∉ [na, fa, ea, xa, (nmF j).tab])
  (htgt : (nmF j).tgt ∉ [na, fa, ea, xa, (nmF j).tab])
  (hup : (nmF j).up ∉ [na, fa, ea, xa, (nmF j).tab])
  (hhist : (nmF j).hist ∉ [na, fa, ea, xa, (nmF j).tab])
  (hnN : (nmF j).nN ∉ btScalars) (hnS : (nmF j).nS ∉ btScalars)
  (hnd5 : ([(nmF j).off, (nmF j).tgt, (nmF j).col, (nmF j).up,
    (nmF j).hist] : List String).Nodup)
  (hscr : ∀ σ, Scr j σ →
    (σ.arrs na).length = 2 ^ S.pal j ∧
    (σ.arrs fa).length = 2 ^ S.pal j * (Kq + 1) ∧
    (σ.arrs ea).length = Kq + 1 ∧ (σ.arrs xa).length = Kq + 1)

include hq hn0B hNLB h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr in
open Classical in
/-- **The leaf block's core** — the lifted leaf stage (`botCom_specW`)
at one edgeless arena, its precondition drawn from the chain's
`BlockPre` and its table postcondition converted to `unrollAux`'s
values at **any** fuel (`unrollAux_of_bot`). Serves the fuel-`0` bottom
block and every level's guarded leaf branch. -/
theorem botBlock_core (k : ℕ) (A : Arena (S.pal j) n₀) (hbot : A.G = ⊥) :
    Spec B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j))
      (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
        (levelFml S j))
      (fun _ σ' => BlockPost S ord k j (hbf j) A (htabF j A) (nmF j) σ')
      (botComK A.N (S.pal j) Kq (levelFml S j)) := by
  have hle : A.N ≤ n₀ := arenaN_le A
  have hbot' : (Impl.ofArena A (htabF j A)).G = ⊥ := hbot
  have hW := botCom_specW (B := B) (hbf j) (nmF j) (Impl.ofArena A (htabF j A))
    hbot' (levelFml S j) hq
    (show A.N < B by omega)
    (show A.N * S.pal j < B from
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) hNLB)
    h2LB
    (show A.N * (levelFml S j).length < B from
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) hTB)
    hnd hoff htgt hup hhist hnN hnS hnd5
  refine (hW.pre ?_).post ?_
  · -- the block precondition lands in the lifted leaf stage's
    rintro σ ⟨hA, htab, hscrσ⟩
    obtain ⟨h1, h2, h3, h4⟩ := hscr σ hscrσ
    exact ⟨hA, h1, h2, h3, h4, htab⟩
  · -- the lifted table values are `unrollAux`'s, at any fuel of an
    -- edgeless arena
    rintro σ σ' - ⟨hA', htab'⟩
    refine ⟨hA', ?_⟩
    rw [unrollAux_of_bot S ord A hbot]
    exact htab'

include hq hn0B hNLB h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr in
open Classical in
/-- **The bottom block, discharged against the chain contract**: at
fuel `0` the block is `botCom` at the level's names — the edgeless
hypothesis is the contract's own fuel-`0` guard. The `< B` bounds are
taken at the root carrier `n₀` once (`arenaN_le` routes every arena
below them); the scratch lengths come out of the level's descriptor;
the name side conditions are the `lv` mechanism's, taken as hypotheses
so the name family stays free (§2 packages their discharge for the
canonical family). -/
theorem botBlock_spec
    (hKB : ∀ A : Arena (S.pal j) n₀,
      botComK A.N (S.pal j) Kq (levelFml S j) ≤ KB 0 j A) :
    BlockSpec B S ord ℓp htabF hbf nmF Adm KB Scr 0 j
      (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
        (levelFml S j)) := by
  intro A hdiag hAdm hbot0
  exact (botBlock_core B S ord ℓp htabF hbf nmF Scr j Kq hq hn0B hNLB h2LB hTB
    hnd hoff htgt hup hhist hnN hnS hnd5 hscr 0 A (hbot0 rfl)).mono (hKB A)

include hq hn0B hNLB h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr in
open Classical in
/-- **The leaf branch of a non-bottom block, discharged** — the
frame-step's guard mechanism (the packet's item 3, leaf half): a
fuel-`k+1` block of the shape

`if nS = 0 then botCom else ⟨the frame body⟩`

satisfies the level's contract as soon as the frame body does **on
edged arenas** (`helse`). The guard's test *is* edgelessness
(`ArenaStW.ns_zero_iff_bot`): on the true branch the arena is `⊥`, the
leaf core runs, and `unrollAux (k+1)`'s leaf clause delivers the
contract's table; on the false branch the arena has an edge and the
frame body takes over. The guard's own `< B` obligation rides
`ns ≤ N² ≤ n₀²` (`ArenaStW.ns_le_sq`). -/
theorem blockSpec_leaf_guard (k : ℕ)
    (hn0B2 : n₀ * n₀ < B)
    (elseCom : Com) (KElse : Arena (S.pal j) n₀ → ℕ)
    (helse : ∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ →
      Spec B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j)) elseCom
        (fun _ σ' => BlockPost S ord (k + 1) j (hbf j) A (htabF j A) (nmF j) σ')
        (KElse A))
    (hKB : ∀ A : Arena (S.pal j) n₀,
      4 + max (botComK A.N (S.pal j) Kq (levelFml S j)) (KElse A)
        ≤ KB (k + 1) j A) :
    BlockSpec B S ord ℓp htabF hbf nmF Adm KB Scr (k + 1) j
      (.ite (.eq (.var (nmF j).nS) (.lit 0))
        (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
          (levelFml S j))
        elseCom) := by
  intro A hdiag hAdm _
  have hle : A.N ≤ n₀ := arenaN_le A
  -- the slot-count cell is below the bound on every block state
  have hnsB : ∀ σ, BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j) σ →
      σ.vars (nmF j).nS < B := by
    intro σ hσ
    have h1 : σ.vars (nmF j).nS ≤ A.N * A.N := hσ.1.ns_le_sq
    have h2 : A.N * A.N ≤ n₀ * n₀ := Nat.mul_le_mul hle hle
    omega
  refine (Spec.ite
    (K := max (botComK A.N (S.pal j) Kq (levelFml S j)) (KElse A))
    ?_ ?_ ?_).mono ?_
  · -- the guard evaluates
    intro σ hσ
    obtain ⟨v, hv, -⟩ := evalB_condEq_isSome (evalB_var (hnsB σ hσ))
      (evalB_lit (show 0 < B by omega))
    exact ⟨v, hv⟩
  · -- the true branch: the guard is edgelessness, the leaf core runs
    intro σ hσ
    obtain ⟨hP, htrue⟩ := hσ
    have hns0 : σ.vars (nmF j).nS = 0 := by
      rw [evalB_condEq_iff] at htrue
      obtain ⟨m, n', hm, hn', heq⟩ := htrue
      rw [evalB_var_iff] at hm
      rw [evalB_lit_iff] at hn'
      obtain ⟨rfl, -⟩ := hm
      obtain ⟨rfl, -⟩ := hn'
      simpa using heq.symm
    have hbot : A.G = ⊥ := hP.1.ns_zero_iff_bot.mp hns0
    exact ((botBlock_core B S ord ℓp htabF hbf nmF Scr j Kq hq hn0B hNLB h2LB
      hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr (k + 1) A hbot).mono
      (le_max_left _ _)) σ hP
  · -- the false branch: the arena has an edge, the frame body takes over
    intro σ hσ
    obtain ⟨hP, hfalse⟩ := hσ
    have hns0 : σ.vars (nmF j).nS ≠ 0 := by
      rw [evalB_condEq_iff] at hfalse
      obtain ⟨m, n', hm, hn', heq⟩ := hfalse
      rw [evalB_var_iff] at hm
      rw [evalB_lit_iff] at hn'
      obtain ⟨rfl, -⟩ := hm
      obtain ⟨rfl, -⟩ := hn'
      simpa using heq.symm
    have hbot : ¬ A.G = ⊥ := fun h => hns0 (hP.1.ns_zero_iff_bot.mpr h)
    exact ((helse A hdiag hAdm hbot).mono (le_max_right _ _)) σ hP
  · -- the guard's cost: `1 + 3` on top of the larger branch
    have := hKB A
    simp only [size_condEq, size_var, size_lit]
    omega

/-! ### The leaf block, with the level's descriptor restored

The leaf block writes only its four scratch arrays, the level table and
the leaf-stage scalars (`warrs_botCom`, `wvars_botCom`), so it touches
no name any descriptor of level `≥ j` reads — and then `specScr`
carries `Scr j` from `BlockPre` straight to the exit. Nothing about the
leaf stage changes; only what its `Spec` is allowed to say. -/

variable (LV LR : ℕ → List String)

/-- The leaf block writes no name the level-`j` descriptor (or any
deeper one) reads, as soon as its five arrays and its scratch scalars
miss the read pools — the syntactic side condition, off
`wvars_botCom`/`warrs_botCom`. -/
theorem botCom_scrFree
    (hbotV : ∀ i, j ≤ i → ∀ y ∈ LV i, y ∉ btScalars)
    (hbotA : ∀ i, j ≤ i → ∀ a ∈ LR i,
      a ∉ ([na, fa, ea, xa, (nmF j).tab] : List String)) :
    ScrFree LV LR j
      (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
        (levelFml S j)) :=
  ⟨fun i hi y hy hmem => hbotV i hi y hy
      (wvars_botCom (nmF j).col na fa ea xa (nmF j).tab (nmF j).nN (S.pal j)
        Kq (levelFml S j) hmem),
   fun i hi a ha hmem => hbotA i hi a ha
      (warrs_botCom (nmF j).col na fa ea xa (nmF j).tab (nmF j).nN (S.pal j)
        Kq (levelFml S j) hmem)⟩

include hq hn0B hNLB h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr in
open Classical in
/-- **The leaf block's core, with the descriptor restored** — verbatim
`botBlock_core` at `BlockPostScr`. The descriptor rides `specScr`: it
enters with `BlockPre` and the leaf stage writes nothing it reads. -/
theorem botBlock_coreScr (k : ℕ) (A : Arena (S.pal j) n₀) (hbot : A.G = ⊥)
    (hfr : ScrFrame Scr LV LR)
    (hfree : ScrFree LV LR j
      (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
        (levelFml S j))) :
    Spec B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j))
      (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
        (levelFml S j))
      (fun _ σ' => BlockPostScr S ord k j (hbf j) A (htabF j A) (Scr j)
        (nmF j) σ')
      (botComK A.N (S.pal j) Kq (levelFml S j)) :=
  (specScr hfr hfree
      (botBlock_core B S ord ℓp htabF hbf nmF Scr j Kq hq hn0B hNLB h2LB hTB
        hnd hoff htgt hup hhist hnN hnS hnd5 hscr k A hbot)).post
    (fun _ _ hpre hqq => ⟨hqq.1, hqq.2.2 hpre.2.2⟩)

include hq hn0B hNLB h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr in
open Classical in
/-- **The bottom block at the strengthened contract** — verbatim
`botBlock_spec` at `BlockSpecScr`. -/
theorem botBlock_specScr
    (hfr : ScrFrame Scr LV LR)
    (hbotV : ∀ i, j ≤ i → ∀ y ∈ LV i, y ∉ btScalars)
    (hbotA : ∀ i, j ≤ i → ∀ a ∈ LR i,
      a ∉ ([na, fa, ea, xa, (nmF j).tab] : List String))
    (hKB : ∀ A : Arena (S.pal j) n₀,
      botComK A.N (S.pal j) Kq (levelFml S j) ≤ KB 0 j A) :
    BlockSpecScr B S ord ℓp htabF hbf nmF Adm KB Scr 0 j
      (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
        (levelFml S j)) := by
  intro A hdiag hAdm hbot0
  exact (botBlock_coreScr B S ord ℓp htabF hbf nmF Scr j Kq hq hn0B hNLB h2LB
    hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr LV LR 0 A (hbot0 rfl) hfr
    (botCom_scrFree S nmF j Kq LV LR hbotV hbotA)).mono (hKB A)

include hq hn0B hNLB h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr in
open Classical in
/-- **The leaf branch of a non-bottom block, at the strengthened
contract** — verbatim `blockSpec_leaf_guard` with both branches now
restoring the level's descriptor: the leaf branch by
`botBlock_coreScr`, the else branch by the residual's own claim. -/
theorem blockSpec_leaf_guardScr (k : ℕ)
    (hn0B2 : n₀ * n₀ < B)
    (hfr : ScrFrame Scr LV LR)
    (hbotV : ∀ i, j ≤ i → ∀ y ∈ LV i, y ∉ btScalars)
    (hbotA : ∀ i, j ≤ i → ∀ a ∈ LR i,
      a ∉ ([na, fa, ea, xa, (nmF j).tab] : List String))
    (elseCom : Com) (KElse : Arena (S.pal j) n₀ → ℕ)
    (helse : ∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth → Adm j A →
      ¬ A.G = ⊥ →
      Spec B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j)) elseCom
        (fun _ σ' => BlockPostScr S ord (k + 1) j (hbf j) A (htabF j A)
          (Scr j) (nmF j) σ')
        (KElse A))
    (hKB : ∀ A : Arena (S.pal j) n₀,
      4 + max (botComK A.N (S.pal j) Kq (levelFml S j)) (KElse A)
        ≤ KB (k + 1) j A) :
    BlockSpecScr B S ord ℓp htabF hbf nmF Adm KB Scr (k + 1) j
      (.ite (.eq (.var (nmF j).nS) (.lit 0))
        (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
          (levelFml S j))
        elseCom) := by
  intro A hdiag hAdm _
  have hle : A.N ≤ n₀ := arenaN_le A
  have hnsB : ∀ σ, BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j) σ →
      σ.vars (nmF j).nS < B := by
    intro σ hσ
    have h1 : σ.vars (nmF j).nS ≤ A.N * A.N := hσ.1.ns_le_sq
    have h2 : A.N * A.N ≤ n₀ * n₀ := Nat.mul_le_mul hle hle
    omega
  refine (Spec.ite
    (K := max (botComK A.N (S.pal j) Kq (levelFml S j)) (KElse A))
    ?_ ?_ ?_).mono ?_
  · -- the guard evaluates
    intro σ hσ
    obtain ⟨v, hv, -⟩ := evalB_condEq_isSome (evalB_var (hnsB σ hσ))
      (evalB_lit (show 0 < B by omega))
    exact ⟨v, hv⟩
  · -- the true branch: the guard is edgelessness, the leaf core runs
    intro σ hσ
    obtain ⟨hP, htrue⟩ := hσ
    have hns0 : σ.vars (nmF j).nS = 0 := by
      rw [evalB_condEq_iff] at htrue
      obtain ⟨m, n', hm, hn', heq⟩ := htrue
      rw [evalB_var_iff] at hm
      rw [evalB_lit_iff] at hn'
      obtain ⟨rfl, -⟩ := hm
      obtain ⟨rfl, -⟩ := hn'
      simpa using heq.symm
    have hbot : A.G = ⊥ := hP.1.ns_zero_iff_bot.mp hns0
    exact ((botBlock_coreScr B S ord ℓp htabF hbf nmF Scr j Kq hq hn0B hNLB
      h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr LV LR (k + 1) A hbot
      hfr (botCom_scrFree S nmF j Kq LV LR hbotV hbotA)).mono
      (le_max_left _ _)) σ hP
  · -- the false branch: the arena has an edge, the frame body takes over
    intro σ hσ
    obtain ⟨hP, hfalse⟩ := hσ
    have hns0 : σ.vars (nmF j).nS ≠ 0 := by
      rw [evalB_condEq_iff] at hfalse
      obtain ⟨m, n', hm, hn', heq⟩ := hfalse
      rw [evalB_var_iff] at hm
      rw [evalB_lit_iff] at hn'
      obtain ⟨rfl, -⟩ := hm
      obtain ⟨rfl, -⟩ := hn'
      simpa using heq.symm
    have hbot : ¬ A.G = ⊥ := fun h => hns0 (hP.1.ns_zero_iff_bot.mpr h)
    exact ((helse A hdiag hAdm hbot).mono (le_max_right _ _)) σ hP
  · -- the guard's cost: `1 + 3` on top of the larger branch
    have := hKB A
    simp only [size_condEq, size_var, size_lit]
    omega

end BotBlock

/-- The leaf block obeys the write discipline as soon as the level's
pools carry its names — the syntactic half of the bottom block, off
the landed frame data. -/
theorem botBlock_owned (LS LA : ℕ → List String) (nmF : ℕ → ArenaNames)
    (j Kq : ℕ) {na fa ea xa : String} (S : Setup L)
    (hLS : ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ a ∈ ([na, fa, ea, xa, (nmF j).tab] : List String), a ∈ LA j) :
    OwnedFrom LS LA j
      (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
        (levelFml S j)) := by
  constructor
  · intro y hy
    exact ⟨j, le_rfl, hLS y
      (wvars_botCom (nmF j).col na fa ea xa (nmF j).tab (nmF j).nN
        (S.pal j) Kq (levelFml S j) hy)⟩
  · intro a ha
    exact ⟨j, le_rfl, hLA a
      (warrs_botCom (nmF j).col na fa ea xa (nmF j).tab (nmF j).nN
        (S.pal j) Kq (levelFml S j) ha)⟩

/-! ## §6 Closing `SolveSpec` -/

open Classical in
/-- **The top scatter stage's obligation** (named residual, seam 2):
some read state `Q` reachable from the root block's postcondition
*plus the top stage's own scratch descriptor* within `Kc`, under which
the verdict expression family `av` reads, per scatter atom of `top`,
the guard bit of the guarded greedy count over the root table —
verbatim the `hscat`/`hav` pair `topCom_spec` consumes. Its discharge
is one `scatterCom_spec_graphCsr` call per atom (the root CSR is the
level-0 region) plus a column extraction from the root table region
(`β ∈ ℱ_0` by `beta_mem_levelFml_zero`), the counts stored in a small
region `av` reads.

`Scr` is the stage's scratch descriptor. The stage needs one because
IMP+ cannot allocate: the scatter machinery needs named `≥ N` scratch
allocations and a bit region for the extracted column, and `BlockPost`
alone carries no allocation facts, so from it every non-arena array may
be empty and no honest scatter program is speccable.

**How it gets here.** The definition is neutral — `Scr` is an arbitrary
state predicate — but the two routes to it are not. The landed
`solveSpec_of_chain` instantiates it at the level-0 descriptor `Scr 0`
and transports it across the chain by `hscrLen0`, i.e. by length
preservation alone; that route is closed to any descriptor carrying the
child-building pass's clean-scratch clause
(`SolveMachPrepSeam.rankScr_not_length_only`). `solveSpec_of_chain_scr`
takes the honest route instead: the chain's contract is `BlockSpecScr`,
whose postcondition *contains* `Scr 0`, so the descriptor arrives
because the root block restores it — no length-only transport
anywhere. -/
def TopScatterSpec (B : ℕ) {L n₀ : ℕ} (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (G : SimpleGraph (Fin n₀))
    (col : Coloring n₀ L) (P Scr : Env → Prop) (scatCom : Com)
    (av : ScatterSentence L → Expr) (Kc : ℕ) : Prop :=
  ∃ Q : Env → Prop,
    Spec B (fun σ => P σ ∧ Scr σ) scatCom (fun _ σ' => Q σ') Kc ∧
    ∀ σ, Q σ → ∀ σa ∈ scatterAtoms S.choice S.φ S.hφ,
      (av σa).evalB B σ = some (scatterBit G
        (Unroll.unrolledTables S ord 0 (rootArena G col)) σa)

open Classical in
/-- **`SolveSpec`, closed by the chain** — the composition theorem of
the leaf. The solve command is the four-stage pipeline

`matCom ; rootLoadCom ; chainCom(ℓ) ; topCom`

(materialize the root arena; load it into the level-0 regions; the
`ℓ+1` blocks; the root evaluation), and `SolveSpec` holds of it at the
summed budget, given:

* the chain's per-input contract at the root (`hchain` — supplied by
  `chainCom_blockSpec` from `botBlock_spec` + the `FrameStep`
  residual),
* the root's admissibility and the degenerate-depth guard (`hAdmRoot`,
  `hdep0` — the run invariant's two facts at the root, F7's),
* the root load (`hload`) and top scatter (`htop`) seam residuals.

The top scatter's scratch descriptor is the level-0 `Scr 0`: the load
establishes it (`BlockPre` carries it), it is length-only
(`hscrLen0` — the instantiator's descriptors always are), and the
chain preserves every array length (`specArrsLength`), so it arrives
at the top stage for free.

The postcondition crosses `topCom_spec` at the root table: the chain's
`unrollAux S.depth 0` **is** `unrolledTables 0` (definitionally, at
`S.depth − 0`), and `verdictCom` lands the exact `SolveSpec` value. -/
theorem solveSpec_of_chain
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ext : List ℕ → String → ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop)
    (frameBody : ℕ → Com → Com) (botB : ℕ → Com)
    (rootLoadCom scatCom : Com) (av : ScatterSentence 0 → Expr)
    (Krl : List ℕ → ℕ) (Kc : ℕ)
    (hq : 1 ≤ q)
    (hextUp : ∀ x ∈ mcD n G c w, ext x "up" = vertexCount x)
    (hAdmRoot : Adm 0 (rootArena G (Impl.trivialColoring n)))
    (hdep0 : (Headline.headlineSetup C hC φ).depth = 0 → G = ⊥)
    (hscrLen0 : ∀ σ σ', Scr 0 σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr 0 σ')
    (hchain : ∀ x ∈ mcD n G c w,
      BlockSpec (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
        nmF Adm KB Scr (Headline.headlineSetup C hC φ).depth 0
        (chainCom frameBody botB (Headline.headlineSetup C hC φ).depth 0))
    (hload : ∀ x ∈ mcD n G c w,
      Spec (mcB q x) (MatIn (ext x) x) rootLoadCom
        (fun _ σ' => BlockPre (Headline.headlineSetup C hC φ) 0 (hbf 0)
          (rootArena G (Impl.trivialColoring n))
          (htabF 0 (rootArena G (Impl.trivialColoring n))) (Scr 0) (nmF 0) σ')
        (Krl x))
    (htop : ∀ x ∈ mcD n G c w,
      TopScatterSpec (mcB q x) (Headline.headlineSetup C hC φ) ord G
        (Impl.trivialColoring n)
        (BlockPost (Headline.headlineSetup C hC φ) ord
          (Headline.headlineSetup C hC φ).depth 0 (hbf 0)
          (rootArena G (Impl.trivialColoring n))
          (htabF 0 (rootArena G (Impl.trivialColoring n))) (nmF 0))
        (Scr 0) scatCom av Kc) :
    SolveSpec C hC φ ord G c w q ext
      (.seq matCom
        (.seq rootLoadCom
          (.seq (chainCom frameBody botB (Headline.headlineSetup C hC φ).depth 0)
            (topCom scatCom (Headline.headlineSetup C hC φ) av))))
      (fun x => matK x + (Krl x +
        (KB (Headline.headlineSetup C hC φ).depth 0
            (rootArena G (Impl.trivialColoring n)) +
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))) := by
  refine solveSpec_of_rest C hC φ ord G c w q ext _ _ hq hextUp ?_
  intro x hx
  obtain ⟨henc, hside⟩ := hx
  have h1B : 1 < mcB q x := one_lt_mcB (three_le_length henc) hq
  -- the chain, at the root arena
  have hchainS := hchain x ⟨henc, hside⟩ (rootArena G (Impl.trivialColoring n))
    (Nat.zero_add _) hAdmRoot (fun h0 => hdep0 h0)
  -- the top scatter residual
  obtain ⟨Q, hscat, hav⟩ := htop x ⟨henc, hside⟩
  -- the root evaluation, at the chain's table state
  have htopS := topCom_spec (mcB q x) (Headline.headlineSetup C hC φ) ord G
    (Impl.trivialColoring n) av rfl h1B hscat hav
  -- chain ; top: the chain preserves every array length, so the
  -- length-only level-0 scratch descriptor crosses it for free and
  -- lands, with the block postcondition, in the top stage's fixed
  -- precondition
  have hct := Spec.seq (specArrsLength hchainS) htopS
    (fun σ σ' hpre hpost => ⟨hpost.1, hscrLen0 σ σ' hpre.2.2 hpost.2⟩)
    (fun _ _ _ _ _ h => h)
  -- load ; (chain ; top)
  have hall := Spec.seq (hload x ⟨henc, hside⟩) hct
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  exact hall

/-! ## §7 The budget, named from the landed terms

The chain's budget family `KB` is abstract above (the `FrameStep`
discharger advertises what its body costs); the definitions below are
its **intended concrete shape**, assembled by name from the landed
per-stage budgets, so that the ledger comparison is bookkeeping. The
per-stage radii follow the landed `Spec`s' parameters (the packet's
hazard): the supports pass runs the shared BFS at the cluster radius
`2R` (the channel bound `hb = 2R+1` is exactly `d+1` there), the
profile calls at `R` (`profilesK`'s own parameter); `restrictK` is
priced at the **parent** degree sum, per `Impl.childCharge`. These
definitions are naming targets — nothing below consumes them yet, and
the `FrameStep` discharge is what will pin them; a mismatch found
there is a finding about *this section*, not about the chain. -/

open Classical in
/-- The per-centre stage budget: restrict → BFS → supports → profiles
→ isolate → the inner block (`nxK`), by the landed budget names, at
the child's own dimensions (`Nc` the cluster size, `nsC` the
pre-isolation child's slot count). -/
noncomputable def centreK (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (ℓpj hbj : ℕ) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (nxK : ℕ) : ℕ :=
  restrictK (Impl.degSum A.G (cluster S A π u)) (childN S A π u) Λ ℓpj hbj
    + (bfsK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
    + (supportsK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) (2 * S.R)
    + (profilesK S.width (relPal Λ) (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) S.R
    + (isolateK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v)
    + nxK))))

open Classical in
/-- The per-centre scatter budget: one guarded `scatterK` call per
scatter atom of the level's decompositions, at the (isolated) child's
dimensions — `ProgFrame.scatterCost`'s shape at the machine budget. -/
noncomputable def centreScatterK (S : Setup L) (j : ℕ)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : ℕ :=
  ((F S j).map fun β =>
    ((scatterAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)).map
      fun σa => scatterK (childN S A π u)
        (∑ v : Fin (childN S A π u), (childArena S A π u).G.degree v)
        σa.r σa.t).sum).sum

open Classical in
/-- **The intended frame budget** (the `FrameStep` discharger's naming
target): the leaf branch at `botComK`, else the cover stage, the
per-centre pipeline with the inner block and the scatter calls, and
the readback — mirroring `ProgCharge.frameChargeMS`'s columns by name.
`Kcov` is the cover stage's (the `CoverStageSpec` discharger's,
`sweepCharge`-shaped); `Kglue` collects the per-centre loads (the
cluster-row copy, the batch assembly, the count region) and the
readback's per-vertex `bcExpr` evaluations — new IMP+ glue, priced by
its discharger. -/
noncomputable def frameK (S : Setup L) (j Kq : ℕ) (A : Arena (S.pal j) n₀)
    (ℓpj hbj : ℕ) (π : Equiv.Perm (Fin A.N)) (Kcov Kglue : ℕ)
    (nxK : Arena (S.pal (j + 1)) n₀ → ℕ) : ℕ :=
  if A.G = ⊥ then botComK A.N (S.pal j) Kq (levelFml S j) else
    Kcov + (((List.finRange A.N).map fun u =>
        centreK S A ℓpj hbj π u (nxK (childArena S A π u))
          + centreScatterK S j A π u).sum
      + Kglue)

open Classical in
/-- **The ledger bridge** (named obligation, priority 5): the solve
budget `Ks` is dominated, input by input, by a constant multiple of
the charge ledger's total (`ProgCharge.mcChargeMS` — the vector
`exists_mcChargeMS_T` prices at `c'·(|x|+1)^{1+ε}`) plus the linear
overhead of the bookends. The per-stage budgets were built to mirror
the ledger's columns by name (`restrictK_le_childCharge`,
`bfsK_le`/`supportsK_le`, `profilesK_le`, `isolateK_le_isolateCharge`,
`scatterK_le`, `botComK_le`); the comparison should be bookkeeping
once `FrameStep` pins `KB` at `frameK` — if a term genuinely does not
fit, that is a loud finding. F7 chains this with
`exists_mcChargeMS_T` and closes the axiom's time bound. -/
def KsChargeBridge (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (covC : (j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ACost String ℕ)
    (Ks : List ℕ → ℕ) : Prop :=
  ∃ cB : ℕ, ∀ x ∈ mcD n G c w,
    Ks x ≤ cB * (chargeTotal
      (mcChargeMS (Headline.headlineSetup C hC φ) ord ℓp htabF covC G
        (Impl.trivialColoring n)) + x.length + 1)

end Lax3Proofs.Prog
