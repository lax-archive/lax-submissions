import Lax3Proofs.SolveCovLoad
import Lax3Proofs.SolveSeamTop
import Lax3Proofs.SolveScrFrameSat
import Lax3Proofs.SolveF7BridgeCover

/-!
# F7 seam — the last two residuals of `solveSpec_closed_scr`, at one
concrete scratch descriptor

`SolveFrameBridge.solveSpec_closed_scr` closes the solve pipeline from
three named residuals.  Two of them are here.  Both already had a
landed discharger, and **both dischargers stop at the same place**: a
hypothesis about the scratch descriptor `Scr` that no *abstract*
descriptor supplies and that the two of them do not even state in the
same currency.

* `SolveGlueLoad.rootLoadSpec_of_csrLoad` (residual 3a, `RootLoadSpec`)
  asks for `hScr0` — `Scr 0` at **every** state whose array lengths
  agree with `MatIn`'s.  That is the length-only shape again, one
  seam further out than the one `rankScr_not_length_only` closed, and
  §5 shows it is not merely unavailable but **refutable** for any
  descriptor implying `RankScr` at the level-0 window.
* `SolveSeamTop.topScatterAll_of` (residual 3b, `TopScatterAll`) asks
  for `hscrT` — four *allocation* clauses (`n ≤ |pa|`, `|ma|`, `|da|`,
  `|atoms| ≤ |tsb|`), which a length-only descriptor cannot be
  *stopped* from having but an abstract one has no reason to have.

And `solveSpec_closed_scr` needs **one** `Scr` meeting both, plus the
leaf block's four exact lengths (`hscr`), plus `ScrFrame` at declared
read pools, plus the two freshness facts.  So the leaf is not two
independent discharges: it is one descriptor, and the two seams closed
at it.

## What is here

* **§1** `f7sSpec_and` — two `Spec`s of the same command and
  precondition may be conjoined (IMP+ is deterministic:
  `BigStep.unique`).  This is what lets the landed root-load assembly
  be reused *unchanged*, at the trivial descriptor, and the descriptor
  be established from the load's frame separately.
* **§2** `F7sLoadExit` — what the concrete root load
  `csrLoadCom ; rootGlueCom` leaves *beyond* `BlockPre`: the level-0
  carrier cell, the exact scalar and array frames, and length
  preservation.  `f7sLoadExit_spec` proves it at the same budget the
  landed assembly charges.
* **§3** `f7s_rootLoadSpec_of_exit` — `RootLoadSpec` for **any** `Scr`
  the exit description establishes.  The length-only `hScr0` is gone;
  what replaces it is a hypothesis a content-carrying descriptor can
  meet, because the load's frame is in it.
* **§4** the concrete descriptor `f7sScr` — `RankScrTower` (the
  landed `SolveScrFrameSat` witness, which already has `ScrFrame`,
  `ScrStep`, `hLVbt`, `hLRbot`) conjoined with the allocation tower
  `F7sAlloc` that carries *every* length clause the chain and the two
  seams ask for.  `ScrFrame.and_lens` is exactly why that conjunction
  is free.
* **§5** anti-vacuity: `f7sEnv` is a concrete state at which the whole
  descriptor holds **with a non-empty window**, and
  `f7sScr_refutes_len` turns that into the refutation of the
  length-only transport.
* **§6** the layout conventions `F7sExt` (also inhabited,
  `f7sExt_f7sLen`), the descriptor established at the load's exit, and
  residual 3a discharged at `f7sScr`, at the concrete command
  `csrLoadCom ; rootGlueCom` and budget `csrLoadK x + (11·n + 8)`.
  `f7s_hScr0_refuted` is the finding: the landed `hScr0` is
  *inconsistent* at this descriptor as soon as `MatIn` has a model, so
  §3's replacement was forced.
* **§7** residual 3b discharged at `f7sScr … 0`, at
  `SolveSeamTop`'s concrete stage and budget.
* **§8** the budget in the ledger's currency: `Krl x ≤ 81·(|x| + 1)`,
  which is `b7c_KsChargeBridge_bucket`'s last standing hypothesis
  `hKrl`, so `f7s_KsChargeBridge_bucket` carries the ledger bridge
  with **no** hypothesis left.
* **§9** the check that it is *one* descriptor:
  `f7s_solveSpec_closed_scr` runs `solveSpec_closed_scr` with the load,
  the top stage, `hfr`, `hLVbt`, `hLRbot` and `hscr` all supplied from
  `f7sScrH`, leaving residual 1 (`FrameStepAllScr`) and the
  instantiator's own data.

## Cost

Nothing here is quantified over the carrier except the load's own
`11·n + 8` glue scan and the CSR pass's landed `70·|x| + 20`, both
linear in the input word.  §8 converts the sum into the ledger's
currency (`c·(|x| + 1)`) explicitly rather than leaving it in a
foreign one.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun
open Lax3Proofs.CoverRoutine

/-! ## §1 Two `Spec`s of one command, conjoined

`Spec` is `∀ σ, P σ → ∃ σ', Run … ∧ Q σ σ'`, and the existential is in
fact unique: IMP+'s semantics is deterministic (`BigStep.unique`).  So
two specifications of the *same* command at the *same* precondition
speak about the same final state and may be conjoined.  Nothing in the
landed kit does this, and it is what keeps §3 from having to re-prove
the root load's `BlockPre` assembly. -/

/-- **Conjunction of specifications**: same bound, same precondition,
same command — the postconditions meet, because the run is unique. -/
theorem f7sSpec_and {B K : ℕ} {P : Env → Prop} {Q R : Env → Env → Prop}
    {c : Com} (h₁ : Spec B P c Q K) (h₂ : Spec B P c R K) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ R σ σ') K := by
  intro σ hσ
  obtain ⟨σ₁, hr₁, hq⟩ := h₁ σ hσ
  obtain ⟨σ₂, hr₂, hr⟩ := h₂ σ hσ
  obtain ⟨k₁, -, hb₁⟩ := hr₁.bigStep
  obtain ⟨k₂, -, hb₂⟩ := hr₂.bigStep
  obtain ⟨rfl, -⟩ := BigStep.unique hb₁ hb₂
  exact ⟨_, hr₁, hq, hr⟩

/-! ## §2 What the concrete root load leaves

The root load the campaign runs is `csrLoadCom ; rootGlueCom` — the
landed deduplicating CSR pass (`SolveCovLoad`) followed by the landed
glue (`SolveGlueLoad`).  `rootLoadSpec_of_csrLoad` reads only its
`BlockPre` output; the descriptor needs its *frame*, which is what the
structure below names.  Every clause is read straight off the two
landed postconditions. -/

/-- **The root load's exit description.** Between the materialized
input and the load's exit: the level-0 carrier cell holds `n`, only
the five scalars `sv.n`, `sv.m`, `rl.k` and the CSR pass's `clScalars`
moved, only the four arrays `sa.o`, `sa.t`, `sa.u`, `cl.d` moved, and
(as for any run) no array changed length. -/
structure F7sLoadExit (n : ℕ) (σ σ' : Env) : Prop where
  /-- The level-0 carrier cell, set by the glue. -/
  nN : σ'.vars (arenaNames 0).nN = n
  /-- The scalar frame of the whole load. -/
  vars : ∀ y, y ≠ (arenaNames 0).nN → y ≠ (arenaNames 0).nS →
    y ≠ "rl.k" → y ∉ clScalars → σ'.vars y = σ.vars y
  /-- The array frame of the whole load. -/
  arrs : ∀ b, b ≠ (arenaNames 0).off → b ≠ (arenaNames 0).tgt →
    b ≠ (arenaNames 0).up → b ≠ "cl.d" → σ'.arrs b = σ.arrs b
  /-- No run changes an array's length. -/
  lens : ∀ b, (σ'.arrs b).length = (σ.arrs b).length

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- **The exit description holds**, at the landed budget: the CSR
pass's `csrLoadK` plus the glue's `11·n + 8`.  The middle condition is
the landed assembly's own (`rootLoadSpec_of_csrLoad`'s first bullet):
the pass leaves `"n"` and the level-0 `up` allocation alone. -/
theorem f7sLoadExit_spec (c w q : ℕ) (ext : List ℕ → String → ℕ)
    (hq : 1 ≤ q)
    (hnB : ∀ x ∈ mcD n G c w, n < mcB q x)
    (hextO : ∀ x ∈ mcD n G c w, n + 1 ≤ ext x "sa.o")
    (hextT : ∀ x ∈ mcD n G c w, 2 * edgeCount x ≤ ext x "sa.t")
    (hextD : ∀ x ∈ mcD n G c w, n ≤ ext x "cl.d")
    (hextUp0 : ∀ x ∈ mcD n G c w, ext x ((arenaNames 0).up) = n)
    (x : List ℕ) (hx : x ∈ mcD n G c w) :
    Spec (mcB q x) (MatIn (ext x) x) (.seq csrLoadCom rootGlueCom)
      (fun σ σ' => F7sLoadExit n σ σ') (csrLoadK x + (11 * n + 8)) := by
  have hvc : vertexCount x = n := hx.1.vertexCount_eq
  have hcsr := rootCsrLoadAll_csrLoadCom (G := G) c w q ext hq hextO hextT
    hextD x hx
  refine Spec.seq hcsr (rootGlueCom_spec (mcB q x) n (hnB x hx)) ?_ ?_
  · -- the pass's output lands in the glue's precondition
    rintro σ σ' hMat ⟨-, hfa, hfv, -⟩
    refine ⟨?_, ?_⟩
    · rw [hfv "n" (by decide) (by decide), hMat.root.n_eq, hvc]
    · rw [hfa _ (by decide) (by decide) (by decide),
        hMat.arrs _ (by decide), hextUp0 x hx]
  · -- assemble the frames of the composite
    rintro σ σ' σ'' - ⟨-, hfa1, hfv1, hlen1⟩ ⟨-, hnN'', hfv2, hfa2, hlen2⟩
    refine ⟨hnN'', ?_, ?_, fun b => (hlen2 b).trans (hlen1 b)⟩
    · intro y hy1 hy2 hy3 hy4
      rw [hfv2 y hy1 hy3, hfv1 y hy2 hy4]
    · intro b hb1 hb2 hb3 hb4
      rw [hfa2 b hb3, hfa1 b hb1 hb2 hb4]

/-! ## §3 `RootLoadSpec` at any descriptor the exit establishes

This is `rootLoadSpec_of_csrLoad` with its one unmeetable hypothesis
replaced.  The landed theorem is used *verbatim*, at the trivial
descriptor `fun _ _ => True` (where its `hScr0` is free); §1 then
conjoins the exit description onto the same run, and the caller
establishes the real descriptor from that. -/

/-- **Residual 3a, at a descriptor the load's frame can establish.**
The command is concrete (`csrLoadCom ; rootGlueCom`), the budget is
concrete (`csrLoadK x + (11·n + 8)`), and the descriptor hypothesis
`hScrExit` is stated against the load's **exit description** rather
than against array lengths alone — so, unlike `hScr0`, it is
satisfiable by a descriptor that carries content (§6). -/
theorem f7s_rootLoadSpec_of_exit (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (c w q : ℕ) (ext : List ℕ → String → ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Scr : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnB : ∀ x ∈ mcD n G c w, n < mcB q x)
    (hpal0 : (Headline.headlineSetup C hC φ).pal 0 = 0)
    (hhtab0 : ∀ (v : Fin (rootArena G (Impl.trivialColoring n)).N)
      (p : Fin (ℓp 0)),
      htabF 0 (rootArena G (Impl.trivialColoring n)) v p = [])
    (hextUp0 : ∀ x ∈ mcD n G c w, ext x ((arenaNames 0).up) = n)
    (hextHist : ∀ x ∈ mcD n G c w,
      n * ℓp 0 * (hbf 0 + 1) ≤ ext x ((arenaNames 0).hist))
    (hextTab : ∀ x ∈ mcD n G c w,
      n * (levelFml (Headline.headlineSetup C hC φ) 0).length
        ≤ ext x ((arenaNames 0).tab))
    (hextO : ∀ x ∈ mcD n G c w, n + 1 ≤ ext x "sa.o")
    (hextT : ∀ x ∈ mcD n G c w, 2 * edgeCount x ≤ ext x "sa.t")
    (hextD : ∀ x ∈ mcD n G c w, n ≤ ext x "cl.d")
    (hScrExit : ∀ x ∈ mcD n G c w, ∀ σ σ', MatIn (ext x) x σ →
      F7sLoadExit n σ σ' → Scr 0 σ') :
    RootLoadSpec C hC φ G c w q ext ℓp htabF hbf Scr
      (.seq csrLoadCom rootGlueCom)
      (fun x => csrLoadK x + (11 * n + 8)) := by
  intro x hx
  have hbase := rootLoadSpec_of_csrLoad C hC φ G c w q ext ℓp htabF hbf
    (fun _ _ => True) "cl.d" clScalars csrLoadCom csrLoadK hnB hpal0 hhtab0
    hextUp0 hextHist hextTab (by decide) (by decide)
    (fun _ _ _ _ _ _ => trivial)
    (rootCsrLoadAll_csrLoadCom (G := G) c w q ext hq hextO hextT hextD) x hx
  have hexit := f7sLoadExit_spec (G := G) c w q ext hq hnB hextO hextT hextD
    hextUp0 x hx
  refine (f7sSpec_and hbase hexit).post ?_
  rintro σ σ' hMat ⟨⟨hA, hT, -⟩, hE⟩
  exact ⟨hA, hT, hScrExit x hx σ σ' hMat hE⟩

/-! ## §4 The concrete descriptor

The descriptor is `SolveScrFrameSat`'s landed witness `RankScrTower`
— the only content clause anything in the chain reads from `Scr`, and
the one already equipped with `ScrFrame`, `ScrStep`, `hscrDown`,
`hLVbt` and `hLRbot` — conjoined with the **allocation tower**
`F7sAlloc`, which collects every *length* clause the pipeline demands
of the descriptor:

* the leaf block's four exact lengths (`solveSpec_closed_scr`'s
  `hscr`) — exact, because `Lib.Csr`-style regions are pinned by
  equality and IMP+'s `store` is `List.set`: **no run changes an
  array's length**, so these must be demanded before the run or they
  are unobtainable;
* the level's rank scratch at `≥ N`, without which `RankScrTower`'s
  own clause is satisfied only by the empty window;
* the top scatter stage's four regions (`topScatterAll_of`'s
  `hscrT`).

Conjoining them is free: `ScrFrame`/`ScrStep` are closed under any
clause read off the array lengths (`ScrFrame.and_lens`,
`ScrStep.and_lens`), which is exactly what `F7sAlloc` is.  Why this
descriptor and not `SolveMachPrepComp.prepScr`: `prepScr` is the
*prep segment's* descriptor and is strictly stronger (it adds
`PrepAlloc`, the batch width, and the root-carrier bounds), so it is
the right one for that seam; here the two seams read only `RankScr`
at the level window plus lengths, and `RankScrTower` is the weakest
descriptor that supplies them — the weakest is the right choice,
since `Scr` sits in these *preconditions*. -/

/-- The top scatter stage's bit region for the extracted β-column. -/
def f7sPa : String := "tp.p"
/-- The top scatter stage's first `≥ N` scratch. -/
def f7sMa : String := "tp.m"
/-- The top scatter stage's second `≥ N` scratch. -/
def f7sDa : String := "tp.d"
/-- The top scatter stage's per-atom slot region. -/
def f7sTsb : String := "tp.s"

/-- **The allocation tower**: every length clause the chain and the
two seams ask of the descriptor at level `j`, over the levels `j … D`
(the leaf regions and the rank scratch are per level; the top stage's
four are global).  All of it is read off array lengths, so it rides
`ScrFrame.and_lens`. -/
def F7sAlloc (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) (j : ℕ)
    (len : String → ℕ) : Prop :=
  (∀ i, j ≤ i → i ≤ D →
      len (botNa i) = 2 ^ pal i ∧
      len (botFa i) = 2 ^ pal i * (Kq + 1) ∧
      len (botEa i) = Kq + 1 ∧
      len (botXa i) = Kq + 1 ∧
      N ≤ len (rankScrName i)) ∧
    N ≤ len f7sPa ∧ N ≤ len f7sMa ∧ N ≤ len f7sDa ∧ nAtoms ≤ len f7sTsb

/-- **The descriptor** the whole pipeline runs at: the landed clean-
scratch tower, fattened by the allocation tower. -/
def f7sScr (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) (j : ℕ) (σ : Env) : Prop :=
  RankScrTower D j σ ∧ F7sAlloc pal Kq nAtoms N D j (fun b => (σ.arrs b).length)

/-- **`ScrFrame`, for the descriptor** — `solveSpec_closed_scr`'s
`hfr`, at the landed read pools. -/
theorem f7sScr_scrFrame (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) :
    ScrFrame (f7sScr pal Kq nAtoms N D) rankScrLV rankScrLR :=
  (rankScrTower_scrFrame D).and_lens (F7sAlloc pal Kq nAtoms N D)

/-- **`ScrStep`, for the descriptor** — what the inner block has
instead of a frame (`SolveChain` §3b). -/
theorem f7sScr_scrStep (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) :
    ScrStep (f7sScr pal Kq nAtoms N D) rankScrLV rankScrLR :=
  (rankScrTower_scrStep D).and_lens (F7sAlloc pal Kq nAtoms N D)

/-- **The descriptor tower's downward step** — `hscrDown`, for the
prep segment. -/
theorem f7sScr_down (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) (j : ℕ) (σ : Env)
    (h : f7sScr pal Kq nAtoms N D j σ) : f7sScr pal Kq nAtoms N D (j + 1) σ :=
  ⟨rankScrTower_down D j σ h.1,
    ⟨fun i hi hiD => h.2.1 i (by omega) hiD, h.2.2⟩⟩

/-- **The leaf block's four exact lengths** — verbatim
`solveSpec_closed_scr`'s `hscr`, at the bottom of the tower. -/
theorem f7sScr_hscr (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) (σ : Env)
    (h : f7sScr pal Kq nAtoms N D D σ) :
    (σ.arrs (botNa D)).length = 2 ^ pal D ∧
      (σ.arrs (botFa D)).length = 2 ^ pal D * (Kq + 1) ∧
      (σ.arrs (botEa D)).length = Kq + 1 ∧
      (σ.arrs (botXa D)).length = Kq + 1 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h.2.1 D le_rfl le_rfl
  exact ⟨h1, h2, h3, h4⟩

/-- **The top scatter stage's four allocation clauses** — verbatim
`topScatterAll_of`'s `hscrT`, at the top of the tower. -/
theorem f7sScr_hscrT (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) (σ : Env)
    (h : f7sScr pal Kq nAtoms N D 0 σ) :
    N ≤ (σ.arrs f7sPa).length ∧ N ≤ (σ.arrs f7sMa).length ∧
      N ≤ (σ.arrs f7sDa).length ∧ nAtoms ≤ (σ.arrs f7sTsb).length :=
  h.2.2

/-! ## §5 The descriptor is inhabited — with a non-empty window

`Scr` sits in the *preconditions* of both seams, so a descriptor
satisfied by nothing would make both discharges true and empty.  It is
inhabited, and inhabited in the way that matters: at a state whose
level windows are **non-empty** and whose scratch is long enough to
hold them — the configuration `rankScr_not_length_only` proves
incompatible with any length-only transport. -/

/-- The length `f7sEnv` gives each array: the leaf regions at their
exact demands (the level is read back off the name's own length — the
`lv` tag is a suffix), everything else long enough for both `N` and
the atom count. -/
def f7sLen (pal : ℕ → ℕ) (Kq nAtoms N : ℕ) (b : String) : ℕ :=
  if b = botNa (b.length - 4) then 2 ^ pal (b.length - 4)
  else if b = botFa (b.length - 4) then 2 ^ pal (b.length - 4) * (Kq + 1)
  else if b = botEa (b.length - 4) then Kq + 1
  else if b = botXa (b.length - 4) then Kq + 1
  else max N nAtoms


/-- The level tag is a suffix, so a name of a length-4 base carries its
own level: this is what lets `f7sLen` be defined name by name. -/
private theorem f7s_lvSub {s : String} (hs : s.length = 4) (i : ℕ) :
    (lv s i).length - 4 = i := by
  rw [lv_length, hs]
  omega

/-- Two distinct length-4 bases stay distinct at any two levels. -/
private theorem f7s_lvNe {s t : String} (hs : s.length = 4) (ht : t.length = 4)
    (hst : s ≠ t) (i k : ℕ) : lv s i ≠ lv t k :=
  lv_ne_of_base_ne (by rw [hs, ht]) hst i k

private theorem f7sLen_botNa (pal : ℕ → ℕ) (Kq nAtoms N i : ℕ) :
    f7sLen pal Kq nAtoms N (botNa i) = 2 ^ pal i := by
  have hi : (botNa i).length - 4 = i := f7s_lvSub (s := "sb.n") (by decide) i
  unfold f7sLen
  rw [hi, if_pos rfl]

private theorem f7sLen_botFa (pal : ℕ → ℕ) (Kq nAtoms N i : ℕ) :
    f7sLen pal Kq nAtoms N (botFa i) = 2 ^ pal i * (Kq + 1) := by
  have hi : (botFa i).length - 4 = i := f7s_lvSub (s := "sb.f") (by decide) i
  have h1 : botFa i ≠ botNa i :=
    f7s_lvNe (s := "sb.f") (t := "sb.n") (by decide) (by decide) (by decide) i i
  unfold f7sLen
  rw [hi, if_neg h1, if_pos rfl]

private theorem f7sLen_botEa (pal : ℕ → ℕ) (Kq nAtoms N i : ℕ) :
    f7sLen pal Kq nAtoms N (botEa i) = Kq + 1 := by
  have hi : (botEa i).length - 4 = i := f7s_lvSub (s := "sb.e") (by decide) i
  have h1 : botEa i ≠ botNa i :=
    f7s_lvNe (s := "sb.e") (t := "sb.n") (by decide) (by decide) (by decide) i i
  have h2 : botEa i ≠ botFa i :=
    f7s_lvNe (s := "sb.e") (t := "sb.f") (by decide) (by decide) (by decide) i i
  unfold f7sLen
  rw [hi, if_neg h1, if_neg h2, if_pos rfl]

private theorem f7sLen_botXa (pal : ℕ → ℕ) (Kq nAtoms N i : ℕ) :
    f7sLen pal Kq nAtoms N (botXa i) = Kq + 1 := by
  have hi : (botXa i).length - 4 = i := f7s_lvSub (s := "sb.x") (by decide) i
  have h1 : botXa i ≠ botNa i :=
    f7s_lvNe (s := "sb.x") (t := "sb.n") (by decide) (by decide) (by decide) i i
  have h2 : botXa i ≠ botFa i :=
    f7s_lvNe (s := "sb.x") (t := "sb.f") (by decide) (by decide) (by decide) i i
  have h3 : botXa i ≠ botEa i :=
    f7s_lvNe (s := "sb.x") (t := "sb.e") (by decide) (by decide) (by decide) i i
  unfold f7sLen
  rw [hi, if_neg h1, if_neg h2, if_neg h3, if_pos rfl]

/-- Every name outside the leaf's four bases gets `max N nAtoms`. -/
private theorem f7sLen_other (pal : ℕ → ℕ) (Kq nAtoms N : ℕ) {s : String}
    (hs : s.length = 4) (h1 : s ≠ "sb.n") (h2 : s ≠ "sb.f") (h3 : s ≠ "sb.e")
    (h4 : s ≠ "sb.x") (i : ℕ) :
    f7sLen pal Kq nAtoms N (lv s i) = max N nAtoms := by
  have hi : (lv s i).length - 4 = i := f7s_lvSub hs i
  have g1 : lv s i ≠ botNa i := f7s_lvNe (t := "sb.n") hs (by decide) h1 i i
  have g2 : lv s i ≠ botFa i := f7s_lvNe (t := "sb.f") hs (by decide) h2 i i
  have g3 : lv s i ≠ botEa i := f7s_lvNe (t := "sb.e") hs (by decide) h3 i i
  have g4 : lv s i ≠ botXa i := f7s_lvNe (t := "sb.x") hs (by decide) h4 i i
  unfold f7sLen
  rw [hi, if_neg g1, if_neg g2, if_neg g3, if_neg g4]

/-- The rank scratch of any level is one of the "other" names. -/
private theorem f7sLen_rankScrName (pal : ℕ → ℕ) (Kq nAtoms N i : ℕ) :
    f7sLen pal Kq nAtoms N (rankScrName i) = max N nAtoms :=
  f7sLen_other pal Kq nAtoms N (s := "sa.r") (by decide) (by decide)
    (by decide) (by decide) (by decide) i

private theorem f7s_arrOf_zero (m : ℕ) :
    arrOf m (fun _ => 0) = List.replicate m (0 : ℕ) := by
  simp [arrOf]

/-- **The witness state**: every cell reads `N`, every array is zeros
at the length `f7sLen` prescribes.  The window of every level is `N`,
so at `0 < N` this is a *non-empty* window with a scratch exactly long
enough to hold it. -/
def f7sEnv (pal : ℕ → ℕ) (Kq nAtoms N : ℕ) : Env where
  vars := fun _ => N
  arrs := fun b => List.replicate (f7sLen pal Kq nAtoms N b) 0
  inp := []
  out := []

/-- The witness's arrays, by name. -/
private theorem f7sEnv_len (pal : ℕ → ℕ) (Kq nAtoms N : ℕ) (b : String) :
    ((f7sEnv pal Kq nAtoms N).arrs b).length = f7sLen pal Kq nAtoms N b := by
  show (List.replicate (f7sLen pal Kq nAtoms N b) 0).length = _
  rw [List.length_replicate]

/-- **The descriptor is inhabited**, at every level of the tower. -/
theorem f7sScr_f7sEnv (pal : ℕ → ℕ) (Kq nAtoms N D j : ℕ) :
    f7sScr pal Kq nAtoms N D j (f7sEnv pal Kq nAtoms N) := by
  have hrank := f7sLen_rankScrName pal Kq nAtoms N
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the clean window, at every level, with the window equal to `N`
    intro i _ _
    show ((f7sEnv pal Kq nAtoms N).arrs (rankScrName i)).take N
      = arrOf N (fun _ => 0)
    show (List.replicate (f7sLen pal Kq nAtoms N (rankScrName i)) 0).take N
      = arrOf N (fun _ => 0)
    rw [hrank i, List.take_replicate, Nat.min_eq_left (Nat.le_max_left _ _),
      f7s_arrOf_zero]
  · -- the leaf regions and the rank scratch, level by level
    intro i _ _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ((f7sEnv pal Kq nAtoms N).arrs (botNa i)).length = _
      rw [f7sEnv_len, f7sLen_botNa]
    · show ((f7sEnv pal Kq nAtoms N).arrs (botFa i)).length = _
      rw [f7sEnv_len, f7sLen_botFa]
    · show ((f7sEnv pal Kq nAtoms N).arrs (botEa i)).length = _
      rw [f7sEnv_len, f7sLen_botEa]
    · show ((f7sEnv pal Kq nAtoms N).arrs (botXa i)).length = _
      rw [f7sEnv_len, f7sLen_botXa]
    · show N ≤ ((f7sEnv pal Kq nAtoms N).arrs (rankScrName i)).length
      rw [f7sEnv_len, hrank i]
      exact Nat.le_max_left _ _
  · show N ≤ ((f7sEnv pal Kq nAtoms N).arrs f7sPa).length
    rw [f7sEnv_len, show f7sPa = lv "tp.p" 0 from rfl,
      f7sLen_other pal Kq nAtoms N (by decide) (by decide) (by decide)
        (by decide) (by decide) 0]
    exact Nat.le_max_left _ _
  · show N ≤ ((f7sEnv pal Kq nAtoms N).arrs f7sMa).length
    rw [f7sEnv_len, show f7sMa = lv "tp.m" 0 from rfl,
      f7sLen_other pal Kq nAtoms N (by decide) (by decide) (by decide)
        (by decide) (by decide) 0]
    exact Nat.le_max_left _ _
  · show N ≤ ((f7sEnv pal Kq nAtoms N).arrs f7sDa).length
    rw [f7sEnv_len, show f7sDa = lv "tp.d" 0 from rfl,
      f7sLen_other pal Kq nAtoms N (by decide) (by decide) (by decide)
        (by decide) (by decide) 0]
    exact Nat.le_max_left _ _
  · show nAtoms ≤ ((f7sEnv pal Kq nAtoms N).arrs f7sTsb).length
    rw [f7sEnv_len, show f7sTsb = lv "tp.s" 0 from rfl,
      f7sLen_other pal Kq nAtoms N (by decide) (by decide) (by decide)
        (by decide) (by decide) 0]
    exact Nat.le_max_right _ _

/-- **The descriptor provably fails the length-only transport.**  Not
merely "the landed `hScr0` is unavailable": at `0 < N` the witness has
a non-empty window and a scratch long enough to hold it, which is the
configuration `rankScr_not_length_only` refutes.  So
`rootLoadSpec_of_csrLoad`'s `hScr0` — and any other length-only
transport of this descriptor — is *unsatisfiable*, and §3's
replacement is not a convenience. -/
theorem f7sScr_refutes_len {pal : ℕ → ℕ} {Kq nAtoms N D j : ℕ} (hjD : j ≤ D)
    (hN : 0 < N)
    (hscrLen : ∀ σ σ', f7sScr pal Kq nAtoms N D j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) →
      f7sScr pal Kq nAtoms N D j σ') : False := by
  refine rankScr_not_length_only (Scr := f7sScr pal Kq nAtoms N D) (j := j)
    (ra := rankScrName j) (nN := (arenaNames j).nN) hscrLen
    (fun _ h => h.1 j le_rfl hjD) (f7sScr_f7sEnv pal Kq nAtoms N D j) hN ?_
  show N ≤ ((f7sEnv pal Kq nAtoms N).arrs (rankScrName j)).length
  rw [f7sEnv_len, f7sLen_rankScrName]
  exact Nat.le_max_left _ _

/-! ## §6 Residual 3a, discharged at the concrete descriptor

What the descriptor asks of the static layout is a family of `ext`
conventions — and only that, because **no run changes an array's
length**: `MatIn` pins every non-arena array at `List.replicate (ext b) 0`,
so every allocation clause of `F7sAlloc` is a fact about `ext` alone and
every content clause is a fact about the load's frame. -/

/-- **The layout conventions the descriptor asks of `ext`.**  Exactly
`F7sAlloc` at level `0`, read on the declared lengths; the leaf regions
are pinned by *equality* (`Lib.Csr` regions are, and `store` is
`List.set`), so they must be declared here or they are unobtainable
later. -/
structure F7sExt (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) (e : String → ℕ) : Prop where
  /-- The leaf's four regions and the rank scratch, at every level. -/
  bot : ∀ i ≤ D, e (botNa i) = 2 ^ pal i ∧
    e (botFa i) = 2 ^ pal i * (Kq + 1) ∧ e (botEa i) = Kq + 1 ∧
    e (botXa i) = Kq + 1 ∧ N ≤ e (rankScrName i)
  /-- The top stage's β-column bit region. -/
  pa : N ≤ e f7sPa
  /-- The top stage's first scratch. -/
  ma : N ≤ e f7sMa
  /-- The top stage's second scratch. -/
  da : N ≤ e f7sDa
  /-- The top stage's per-atom slot region. -/
  tsb : nAtoms ≤ e f7sTsb

/-- A level-tagged name of a length-4 base is never one of the parse's
arrays: those are shorter. -/
private theorem f7s_lv_notMem_matArrays {s : String} (hs : s.length = 4)
    (i : ℕ) : lv s i ∉ matArrays := by
  intro h
  have hl : ∀ t ∈ matArrays, t.length ≤ 3 := by decide
  have h2 := hl _ h
  rw [lv_length, hs] at h2
  omega

/-- The same for the parse's scalars. -/
private theorem f7s_lv_notMem_matScalars {s : String} (hs : s.length = 4)
    (i : ℕ) : lv s i ∉ matScalars := by
  intro h
  have hl : ∀ t ∈ matScalars, t.length ≤ 3 := by decide
  have h2 := hl _ h
  rw [lv_length, hs] at h2
  omega

/-- The CSR pass's scalars are level-`0` names of four other bases. -/
private theorem f7s_lv_notMem_clScalars {s : String} (hs : s.length = 4)
    (h1 : s ≠ "cl.u") (h2 : s ≠ "cl.j") (h3 : s ≠ "cl.p") (h4 : s ≠ "cl.w")
    (i : ℕ) : lv s i ∉ clScalars := by
  simp only [clScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨f7s_lvNe hs (by decide) h1 i 0, f7s_lvNe hs (by decide) h2 i 0,
    f7s_lvNe hs (by decide) h3 i 0, f7s_lvNe hs (by decide) h4 i 0⟩

/-- Every allocation the descriptor names survives the load unchanged in
length — because no run changes a length at all. -/
private theorem f7s_len_eq {e : String → ℕ} {x : List ℕ} {σ σ' : Env} {N : ℕ}
    (hM : MatIn e x σ) (hX : F7sLoadExit N σ σ') {s : String} (hs : s.length = 4)
    (i : ℕ) : (σ'.arrs (lv s i)).length = e (lv s i) := by
  rw [hX.lens, hM.arrs _ (f7s_lv_notMem_matArrays hs i), List.length_replicate]

/-- **The descriptor, established at the load's exit.**  The level-`0`
window is the only non-trivial clause: the load sets that cell to `n`
and touches neither the rank scratch nor any deeper carrier cell, so at
every level `i > 0` the cell is still `MatIn`'s zero and the clause is
`take 0 = []`. -/
theorem f7sScr_of_loadExit {pal : ℕ → ℕ} {Kq nAtoms N D : ℕ}
    {e : String → ℕ} {x : List ℕ} {σ σ' : Env}
    (hE : F7sExt pal Kq nAtoms N D e) (hM : MatIn e x σ)
    (hX : F7sLoadExit N σ σ') : f7sScr pal Kq nAtoms N D 0 σ' := by
  -- the deeper carrier cells are untouched, hence still `MatIn`'s zero
  have hcell : ∀ i : ℕ, 0 < i → σ'.vars (arenaNames i).nN = 0 := by
    intro i hi
    have h1 : (arenaNames i).nN ≠ (arenaNames 0).nN :=
      lv_ne_of_level_ne (s := "sv.n") (t := "sv.n") rfl (by omega)
    have h2 : (arenaNames i).nN ≠ (arenaNames 0).nS :=
      f7s_lvNe (s := "sv.n") (t := "sv.m") (by decide) (by decide) (by decide) i 0
    have h3 : (arenaNames i).nN ≠ "rl.k" :=
      f7s_lvNe (s := "sv.n") (t := "rl.k") (by decide) (by decide) (by decide) i 0
    have h4 : (arenaNames i).nN ∉ clScalars :=
      f7s_lv_notMem_clScalars (s := "sv.n") (by decide) (by decide) (by decide)
        (by decide) (by decide) i
    rw [hX.vars _ h1 h2 h3 h4]
    exact hM.zero _ (f7s_lv_notMem_matScalars (s := "sv.n") (by decide) i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the clean-scratch tower
    intro i _ hiD
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · -- level 0: the window is `n`, and the scratch is `MatIn`'s zeros
      have harr : σ'.arrs (rankScrName 0) = List.replicate (e (rankScrName 0)) 0 := by
        rw [hX.arrs _ (by decide) (by decide) (by decide) (by decide)]
        exact hM.arrs _ (f7s_lv_notMem_matArrays (s := "sa.r") (by decide) 0)
      show (σ'.arrs (rankScrName 0)).take (σ'.vars (arenaNames 0).nN)
        = arrOf (σ'.vars (arenaNames 0).nN) (fun _ => 0)
      rw [hX.nN, harr, List.take_replicate,
        Nat.min_eq_left (hE.bot 0 (Nat.zero_le _)).2.2.2.2, f7s_arrOf_zero]
    · -- every deeper level: the window is empty
      show (σ'.arrs (rankScrName i)).take (σ'.vars (arenaNames i).nN)
        = arrOf (σ'.vars (arenaNames i).nN) (fun _ => 0)
      rw [hcell i hi]
      simp [arrOf]
  · -- the leaf regions and the rank scratch, at the declared lengths
    intro i _ hiD
    obtain ⟨e1, e2, e3, e4, e5⟩ := hE.bot i hiD
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (f7s_len_eq hM hX (s := "sb.n") (by decide) i).trans e1
    · exact (f7s_len_eq hM hX (s := "sb.f") (by decide) i).trans e2
    · exact (f7s_len_eq hM hX (s := "sb.e") (by decide) i).trans e3
    · exact (f7s_len_eq hM hX (s := "sb.x") (by decide) i).trans e4
    · exact e5.trans_eq (f7s_len_eq hM hX (s := "sa.r") (by decide) i).symm
  · exact hE.pa.trans_eq (f7s_len_eq hM hX (s := "tp.p") (by decide) 0).symm
  · exact hE.ma.trans_eq (f7s_len_eq hM hX (s := "tp.m") (by decide) 0).symm
  · exact hE.da.trans_eq (f7s_len_eq hM hX (s := "tp.d") (by decide) 0).symm
  · exact hE.tsb.trans_eq (f7s_len_eq hM hX (s := "tp.s") (by decide) 0).symm

/-- **The layout conventions are satisfiable**, by the very length
function §5's witness state uses.  `F7sExt` sits in §6's *hypotheses*,
so this is the second anti-vacuity obligation; it is met by
`f7sLen`, and it does not collide with the load's own conventions
(`hextO`/`hextT`/`hextD`/`hextUp0`/`hextHist`/`hextTab`), which
constrain the disjoint name set `sa.o`, `sa.t`, `sa.u`, `sa.h`,
`sa.b`, `cl.d` — none of which `F7sExt` mentions. -/
theorem f7sExt_f7sLen (pal : ℕ → ℕ) (Kq nAtoms N D : ℕ) :
    F7sExt pal Kq nAtoms N D (f7sLen pal Kq nAtoms N) where
  bot i _ := ⟨f7sLen_botNa pal Kq nAtoms N i, f7sLen_botFa pal Kq nAtoms N i,
    f7sLen_botEa pal Kq nAtoms N i, f7sLen_botXa pal Kq nAtoms N i,
    (f7sLen_rankScrName pal Kq nAtoms N i).symm ▸ Nat.le_max_left N nAtoms⟩
  pa := (f7sLen_other pal Kq nAtoms N (s := "tp.p") (by decide) (by decide)
    (by decide) (by decide) (by decide) 0).symm ▸ Nat.le_max_left N nAtoms
  ma := (f7sLen_other pal Kq nAtoms N (s := "tp.m") (by decide) (by decide)
    (by decide) (by decide) (by decide) 0).symm ▸ Nat.le_max_left N nAtoms
  da := (f7sLen_other pal Kq nAtoms N (s := "tp.d") (by decide) (by decide)
    (by decide) (by decide) (by decide) 0).symm ▸ Nat.le_max_left N nAtoms
  tsb := (f7sLen_other pal Kq nAtoms N (s := "tp.s") (by decide) (by decide)
    (by decide) (by decide) (by decide) 0).symm ▸ Nat.le_max_right N nAtoms

/-- **The landed `hScr0` is refuted at this descriptor, not merely
avoided.**  `SolveGlueLoad.rootLoadSpec_of_csrLoad`'s descriptor
hypothesis is `Scr 0` at *every* state whose array lengths agree with a
`MatIn` state's.  As soon as `MatIn` has a model at all — which it does
whenever the pipeline runs — that hypothesis is **inconsistent** with a
descriptor that demands a clean window of positive size: raise the
level-0 carrier cell to `N` and flip one scratch cell, and every length
is unchanged while the window is dirty.

So §3 does not replace `hScr0` out of taste.  The landed theorem, at
this descriptor, proves nothing: it is the exact-length/length-only
trap once more, at the root load rather than at the prep segment. -/
theorem f7s_hScr0_refuted {pal : ℕ → ℕ} {Kq nAtoms N D : ℕ}
    {e : String → ℕ} {x : List ℕ} {σ : Env} (hN : 0 < N) (hM : MatIn e x σ)
    (hScr0 : ∀ σ₀ σ', MatIn e x σ₀ →
      (∀ b, (σ'.arrs b).length = (σ₀.arrs b).length) →
      f7sScr pal Kq nAtoms N D 0 σ') : False := by
  -- the base state: `MatIn`'s, with the level-0 carrier cell raised
  have hbase := hScr0 σ (σ.setVar (arenaNames 0).nN N) hM (fun b => by simp)
  refine rankScr_not_length_only
    (Scr := fun (_ : ℕ) τ => ∀ b, (τ.arrs b).length = (σ.arrs b).length)
    (j := 0) (ra := rankScrName 0) (nN := (arenaNames 0).nN)
    (fun τ τ' hτ hlen b => (hlen b).trans (hτ b))
    (fun τ hτ => (hScr0 σ τ hM hτ).1 0 le_rfl (Nat.zero_le _))
    (σ := σ.setVar (arenaNames 0).nN N) (fun b => by simp) ?_ ?_
  · show 0 < (σ.setVar (arenaNames 0).nN N).vars (arenaNames 0).nN
    simpa using hN
  · show (σ.setVar (arenaNames 0).nN N).vars (arenaNames 0).nN
      ≤ ((σ.setVar (arenaNames 0).nN N).arrs (rankScrName 0)).length
    have := (hbase.2.1 0 le_rfl (Nat.zero_le _)).2.2.2.2
    simpa using this

open Classical in
/-- **The descriptor, at the headline schedule's own parameters** — the
form both seams and `solveSpec_closed_scr` consume: the tower runs to
the schedule depth, the slot region to the number of top scatter
atoms. -/
noncomputable def f7sScrH (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (Kq N : ℕ) : ℕ → Env → Prop :=
  f7sScr (Headline.headlineSetup C hC φ).pal Kq
    (scatterAtoms (Headline.headlineSetup C hC φ).choice
      (Headline.headlineSetup C hC φ).φ
      (Headline.headlineSetup C hC φ).hφ).length
    N (Headline.headlineSetup C hC φ).depth

open Classical in
/-- **Residual 3a of `solveSpec_closed_scr`, discharged.**
`RootLoadSpec` holds — verbatim — at the concrete command
`csrLoadCom ; rootGlueCom`, the concrete budget
`csrLoadK x + (11·n + 8) = 70·|x| + 11·n + 28`, and the **concrete,
content-carrying** descriptor `f7sScrH`.  Every hypothesis is an `ext`
convention, a word bound, or the two landed structural facts about the
root (`pal 0 = 0`, the empty channel) — no length-only transport
anywhere, and §5 shows there could not have been one. -/
theorem f7s_rootLoadSpec (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (c w q : ℕ) (ext : List ℕ → String → ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Kq : ℕ)
    (hq : 1 ≤ q)
    (hnB : ∀ x ∈ mcD n G c w, n < mcB q x)
    (hpal0 : (Headline.headlineSetup C hC φ).pal 0 = 0)
    (hhtab0 : ∀ (v : Fin (rootArena G (Impl.trivialColoring n)).N)
      (p : Fin (ℓp 0)),
      htabF 0 (rootArena G (Impl.trivialColoring n)) v p = [])
    (hextUp0 : ∀ x ∈ mcD n G c w, ext x ((arenaNames 0).up) = n)
    (hextHist : ∀ x ∈ mcD n G c w,
      n * ℓp 0 * (hbf 0 + 1) ≤ ext x ((arenaNames 0).hist))
    (hextTab : ∀ x ∈ mcD n G c w,
      n * (levelFml (Headline.headlineSetup C hC φ) 0).length
        ≤ ext x ((arenaNames 0).tab))
    (hextO : ∀ x ∈ mcD n G c w, n + 1 ≤ ext x "sa.o")
    (hextT : ∀ x ∈ mcD n G c w, 2 * edgeCount x ≤ ext x "sa.t")
    (hextD : ∀ x ∈ mcD n G c w, n ≤ ext x "cl.d")
    (hextScr : ∀ x ∈ mcD n G c w,
      F7sExt (Headline.headlineSetup C hC φ).pal Kq
        (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ).length n
        (Headline.headlineSetup C hC φ).depth (ext x)) :
    RootLoadSpec C hC φ G c w q ext ℓp htabF hbf (f7sScrH C hC φ Kq n)
      (.seq csrLoadCom rootGlueCom)
      (fun x => csrLoadK x + (11 * n + 8)) :=
  f7s_rootLoadSpec_of_exit C hC φ c w q ext ℓp htabF hbf _ hq hnB hpal0 hhtab0
    hextUp0 hextHist hextTab hextO hextT hextD
    (fun x hx _ _ hM hX => f7sScr_of_loadExit (hextScr x hx) hM hX)

/-! ## §7 Residual 3b, discharged at the same descriptor

`SolveSeamTop.topScatterAll_of` already discharges `TopScatterAll` at a
real scatter stage; its one descriptor hypothesis `hscrT` is exactly
`F7sAlloc`'s global half.  The four scratch names are this file's, so
their freshness against the level-0 family and their mutual
distinctness are decided. -/

open Classical in
/-- **Residual 3b of `solveSpec_closed_scr`, discharged at the same
descriptor.**  `TopScatterAll` holds — verbatim — of `SolveSeamTop`'s
concrete stage at the canonical level-0 names and this file's four
scratch regions, with the top stage's scratch descriptor being the very
`f7sScrH … 0` the root load establishes.  What was two seams becomes
one descriptor. -/
theorem f7s_topScatterAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Kq : ℕ)
    (hq : 1 ≤ q)
    (hB : ∀ x ∈ mcD n G c w, n < mcB q x ∧ n * n < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ) 0).length < mcB q x ∧
      (scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ).length < mcB q x)
    (hatomB : ∀ x ∈ mcD n G c w,
      ∀ σa ∈ scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ,
      σa.r + 2 < mcB q x ∧ σa.t < mcB q x) :
    TopScatterAll C hC φ ord G c w q ℓp htabF hbf (f7sScrH C hC φ Kq n 0)
      (topAtomsCom (arenaNames 0) f7sPa f7sMa f7sDa f7sTsb
        (levelFml (Headline.headlineSetup C hC φ) 0).length
        (fun σa => memIdx (levelFml (Headline.headlineSetup C hC φ) 0) σa.β)
        (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ) 0)
      (fun σa => .get f7sTsb (.lit (memIdx
        (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ) σa)))
      (topScatK n (∑ v : Fin n, G.degree v)
        (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ)) :=
  topScatterAll_of C hC φ ord G c w q ℓp htabF hbf _ f7sPa f7sMa f7sDa f7sTsb hq
    (fun σ hσ => f7sScr_hscrT _ Kq _ n _ σ hσ) hB hatomB
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## §8 The budget, in the ledger's currency

`b7c_KsChargeBridge_bucket` carries the whole ledger comparison with one
hypothesis standing: `hKrl`, the root load's budget against
`crl·(|x| + 1)`.  §6's budget is `csrLoadK x + (11·n + 8)`, and the
carrier is bounded by the input word (`EncodesGraph.length_eq`), so the
constant is explicit and small. -/

/-- **The root load's budget is linear in the input word**, at the
explicit constant `81`.  Both terms are already in the ledger's
currency — `70·|x| + 20` is the CSR pass's, `11·n + 8` the glue scan's
and `n ≤ |x|` — so nothing is left in a foreign one. -/
theorem f7s_Krl_le (c w : ℕ) :
    ∀ x ∈ mcD n G c w, csrLoadK x + (11 * n + 8) ≤ 81 * (x.length + 1) := by
  intro x hx
  have hlen : x.length = 3 + n + 2 * edgeCount x := hx.1.length_eq
  simp only [csrLoadK]
  omega

open Lax11.GraphEncoding in
open Classical in
/-- **The ledger bridge, with no hypothesis left.**  Verbatim
`b7c_KsChargeBridge_bucket` at the root load this file discharges:
`Krl` is `csrLoadK x + (11·n + 8)`, and its `hKrl` is §8's bound at
`crl = 81`.  Everything the bridge needed is now supplied. -/
theorem f7s_KsChargeBridge_bucket
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) (Kq a b c : ℕ)
    (hG : C n G) (cw ww : ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (Kc : ℕ) (av : ScatterSentence 0 → Expr) :
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
        (fun x => matK x + ((csrLoadK x + (11 * n + 8)) +
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
            (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))) :=
  b7c_KsChargeBridge_bucket C hC φ hε ℓp Kq a b c G hG cw ww htabF
    (fun x => csrLoadK x + (11 * n + 8)) Kc 81 av (f7s_Krl_le cw ww)

/-! ## §9 The two seams, composed at the one descriptor

The point of doing both residuals at *one* descriptor is that
`solveSpec_closed_scr` consumes them together and asks the descriptor
for four more things besides — `ScrFrame` at declared read pools, the
two freshness facts, and the leaf block's exact lengths.  The theorem
below is the check that all six demands are met by the *same*
`f7sScrH`, so nothing here is a discharge that only works in
isolation.  What is left standing is residual 1 (`FrameStepAllScr`)
and the instantiator's own data — the frame body, its budget family
`KB`, the admissibility predicate and the name pools. -/

open Classical in
/-- **`SolveSpec`, closed from residual 1 alone.**  Verbatim
`solveSpec_closed_scr` with its root load, its top scatter and its
whole scratch descriptor supplied by this file: the pipeline is
concrete except for the frame body, and the two seam budgets are
concrete.  Every hypothesis that mentions the descriptor is
discharged here (`hfr`, `hLVbt`, `hLRbot`, `hscr`); the rest are the
instantiator's. -/
theorem f7s_solveSpec_closed_scr
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) (c w q : ℕ) (ext : List ℕ → String → ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (LS LA : ℕ → List String) (frameBody : ℕ → Com → Com) (Kq : ℕ)
    (hq : 1 ≤ q)
    (hextUp : ∀ x ∈ mcD n G c w, ext x "up" = vertexCount x)
    (hAdmRoot : Adm 0 (rootArena G (Impl.trivialColoring n)))
    (hdep0 : (Headline.headlineSetup C hC φ).depth = 0 → G = ⊥)
    -- the load's own conventions and bounds
    (hnB : ∀ x ∈ mcD n G c w, n < mcB q x)
    (hpal0 : (Headline.headlineSetup C hC φ).pal 0 = 0)
    (hhtab0 : ∀ (v : Fin (rootArena G (Impl.trivialColoring n)).N)
      (p : Fin (ℓp 0)),
      htabF 0 (rootArena G (Impl.trivialColoring n)) v p = [])
    (hextUp0 : ∀ x ∈ mcD n G c w, ext x ((arenaNames 0).up) = n)
    (hextHist : ∀ x ∈ mcD n G c w,
      n * ℓp 0 * (hbf 0 + 1) ≤ ext x ((arenaNames 0).hist))
    (hextTab : ∀ x ∈ mcD n G c w,
      n * (levelFml (Headline.headlineSetup C hC φ) 0).length
        ≤ ext x ((arenaNames 0).tab))
    (hextO : ∀ x ∈ mcD n G c w, n + 1 ≤ ext x "sa.o")
    (hextT : ∀ x ∈ mcD n G c w, 2 * edgeCount x ≤ ext x "sa.t")
    (hextD : ∀ x ∈ mcD n G c w, n ≤ ext x "cl.d")
    (hextScr : ∀ x ∈ mcD n G c w,
      F7sExt (Headline.headlineSetup C hC φ).pal Kq
        (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ).length n
        (Headline.headlineSetup C hC φ).depth (ext x))
    -- the top stage's word bounds
    (hBtop : ∀ x ∈ mcD n G c w, n < mcB q x ∧ n * n < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ) 0).length < mcB q x ∧
      (scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ).length < mcB q x)
    (hatomB : ∀ x ∈ mcD n G c w,
      ∀ σa ∈ scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ,
      σa.r + 2 < mcB q x ∧ σa.t < mcB q x)
    -- the bottom level's bookkeeping (the instantiator's)
    (hKq : ∀ β ∈ levelFml (Headline.headlineSetup C hC φ)
      (Headline.headlineSetup C hC φ).depth, qdepth β ≤ Kq)
    (hBbot : ∀ x ∈ mcD n G c w,
      n < mcB q x ∧
      n * (Headline.headlineSetup C hC φ).pal
        (Headline.headlineSetup C hC φ).depth < mcB q x ∧
      2 ^ (Headline.headlineSetup C hC φ).pal
        (Headline.headlineSetup C hC φ).depth * (Kq + 1) < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ)
        (Headline.headlineSetup C hC φ).depth).length < mcB q x)
    (hKB0 : ∀ A : Arena ((Headline.headlineSetup C hC φ).pal
        (Headline.headlineSetup C hC φ).depth) n,
      botComK A.N ((Headline.headlineSetup C hC φ).pal
          (Headline.headlineSetup C hC φ).depth) Kq
          (levelFml (Headline.headlineSetup C hC φ)
            (Headline.headlineSetup C hC φ).depth)
        ≤ KB 0 (Headline.headlineSetup C hC φ).depth A)
    (hLS : ∀ j, ∀ y ∈ btScalars, y ∈ LS j)
    (hLA : ∀ j, ∀ a ∈ ([botNa j, botFa j, botEa j, botXa j,
      (arenaNames j).tab] : List String), a ∈ LA j)
    -- residual 1, the only seam left
    (hstep : FrameStepAllScr C hC φ ord G c w q ℓp htabF hbf Adm KB
      (f7sScrH C hC φ Kq n) LS LA frameBody) :
    SolveSpec C hC φ ord G c w q ext
      (.seq matCom
        (.seq (.seq csrLoadCom rootGlueCom)
          (.seq (chainCom frameBody
              (canonBotB (Headline.headlineSetup C hC φ) Kq)
              (Headline.headlineSetup C hC φ).depth 0)
            (topCom
              (topAtomsCom (arenaNames 0) f7sPa f7sMa f7sDa f7sTsb
                (levelFml (Headline.headlineSetup C hC φ) 0).length
                (fun σa =>
                  memIdx (levelFml (Headline.headlineSetup C hC φ) 0) σa.β)
                (scatterAtoms (Headline.headlineSetup C hC φ).choice
                  (Headline.headlineSetup C hC φ).φ
                  (Headline.headlineSetup C hC φ).hφ) 0)
              (Headline.headlineSetup C hC φ)
              (fun σa => .get f7sTsb (.lit (memIdx
                (scatterAtoms (Headline.headlineSetup C hC φ).choice
                  (Headline.headlineSetup C hC φ).φ
                  (Headline.headlineSetup C hC φ).hφ) σa)))))))
      (fun x => matK x + ((csrLoadK x + (11 * n + 8)) +
        (KB (Headline.headlineSetup C hC φ).depth 0
            (rootArena G (Impl.trivialColoring n)) +
          (topScatK n (∑ v : Fin n, G.degree v)
              (scatterAtoms (Headline.headlineSetup C hC φ).choice
                (Headline.headlineSetup C hC φ).φ
                (Headline.headlineSetup C hC φ).hφ) +
            topEvalCost (Headline.headlineSetup C hC φ)
              (fun σa => .get f7sTsb (.lit (memIdx
                (scatterAtoms (Headline.headlineSetup C hC φ).choice
                  (Headline.headlineSetup C hC φ).φ
                  (Headline.headlineSetup C hC φ).hφ) σa))))))) :=
  solveSpec_closed_scr C hC φ ord G c w q ext ℓp htabF hbf Adm KB
    (f7sScrH C hC φ Kq n) LS LA rankScrLV rankScrLR frameBody
    (.seq csrLoadCom rootGlueCom) _ _ _ _ Kq hq hextUp hAdmRoot hdep0
    (f7sScr_scrFrame _ _ _ _ _) rankScrLV_notMem_bt rankScrLR_notMem_bot
    hKq hBbot (fun σ hσ => f7sScr_hscr _ Kq _ n _ σ hσ) hKB0 hLS hLA hstep
    (f7s_rootLoadSpec C hC φ c w q ext ℓp htabF hbf Kq hq hnB hpal0 hhtab0
      hextUp0 hextHist hextTab hextO hextT hextD hextScr)
    (f7s_topScatterAll C hC φ ord c w q ℓp htabF hbf Kq hq hBtop hatomB)

/-! ## §10 Axiom profile -/

#print axioms f7sSpec_and
#print axioms f7sLoadExit_spec
#print axioms f7s_rootLoadSpec_of_exit
#print axioms f7sScr_scrFrame
#print axioms f7sScr_scrStep
#print axioms f7sScr_down
#print axioms f7sScr_hscr
#print axioms f7sScr_hscrT
#print axioms f7sScr_f7sEnv
#print axioms f7sScr_refutes_len
#print axioms f7sScr_of_loadExit
#print axioms f7sExt_f7sLen
#print axioms f7s_hScr0_refuted
#print axioms f7s_rootLoadSpec
#print axioms f7s_topScatterAll
#print axioms f7s_Krl_le
#print axioms f7s_KsChargeBridge_bucket
#print axioms f7s_solveSpec_closed_scr

end Lax3Proofs.Prog
