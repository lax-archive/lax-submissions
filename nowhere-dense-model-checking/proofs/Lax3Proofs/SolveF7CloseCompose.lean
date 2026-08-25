import Lax3Proofs.SolveF7CloseQ
import Lax3Proofs.SolveF7BridgeCover

/-!
# F7-c, part 3 — the pipeline command, the layout obstruction, and the
composition with `solveSpec_closed_scr`

Two things stand between `SolveFrameBridge.solveSpec_closed_scr` and
`SolveF7Close.f7close_exists_of_solveSpec`, and this file names both
exactly.

## §2 The budget seam (repaired here)

`solveSpec_closed_scr` concludes `SolveSpec` at

    fun x => matK x + (Krl x + (KB ℓ 0 (rootArena G col) + (Kc + topEvalCost S av)))

whose third summand mentions **`G`**. The axiom's `T` is fixed before
`n` and `G`, so this cannot be the `Ks` the close consumes.
`f7_solveSpec_mono_Ks` (`SolveF7CloseQ` §5) repairs it — `Spec` is
monotone in its budget — at the cost of one hypothesis `hdom`: a
uniform `Ks` dominating the graph-indexed budget on every admissible
input. `f7close_of_closed_scr` below is the composition, and it asks
for `solveSpec_closed_scr`'s conclusion ∀-quantified rather than
re-listing its thirty hypotheses, so a caller that has the closure in
hand applies it in one step.

## §1 The layout obstruction (found here, repaired in
`ProgCodegenLayout`)

`ProgCodegenLayout.mcLayout` used to fix `temps = 2`.
`Lax13Proofs.Compile.Expr.Ok` charges one temporary per level of *left*
nesting: `Expr.Ok L (.bin _ e f) d` asks for `Expr.Ok L e (d+1)` and
`d < L.temps`. The root evaluation compiles the sentence's boolean
combination into one expression —
`SolveMatTop.verdictCom S av = .assign "verdict" (bcExpr av (top S))`,
and `bcExpr` sends `.and b c` to `.mul (bcExpr av b) (bcExpr av c)`,
nesting **left**. So a combination with three nested conjunctions on
the left already needs `temps ≥ 3`, and
`f7_bcExpr_not_ok_at_mcLayout_two` exhibits one that does not compile
at two — for every extension `eS`/`eA` and every read valuation `av`.

`ProgCodegen.mc_computesInTime_of_solveSpec`'s hypothesis
`hokS : Com.Ok (mcLayout eS eA 2) solveCom` was therefore
**unsatisfiable for the real pipeline** at every sentence whose root
combination nests three conjunctions on the left — which is most of
them. Both `ProgCodegenLayout`'s docstring ("a bigger `temps` only
shifts the constant in `hspan`") and `SolveMatTop`'s layout note ("F7
instantiates the layout with `temps ≥` the compiled combination's
depth") said F7 should raise `temps`, and `mcLayout` had no `temps`
argument to raise.

It now does: `mcLayout eS eA t`, with

* `mcLayout_span_le`/`mcLayout_fitsWords`'s `hspan`
  `9 + t + |eS| + (2 + |eA|)·q ≤ c` (the old literal `11` was `2 + 9`,
  the fixed `temps` plus the nine parse scalars);
* `parseCom_ok` at `2 ≤ t`, `matCom_ok` at `0 < t`, `mcCom_ok`'s
  epilogue at `0 < t`;
* `Com.Ok` monotone in `temps` (`com_ok_mono_temps`), so every landed
  compilability proof is replayed at its own `temps` and transported.

Nothing else in the tower depends on `temps` — `Layout.const` is
`3·idxLen + 13` and `idxLen` counts *arrays* (`mcLayout_const_eq`), so
the machine constant is untouched and the axiom's `c` absorbs the span
exactly as before. `SolveF7Temps` computes the `t` the pipeline
actually needs and shows it is a constant of the schedule; §1 below
keeps the negative witness as the record of the defect and adds its
positive counterpart.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver Lax3Proofs.CoverRoutine

variable {L : ℕ}

/-! ## §0 The pre-sized parse arrays — F7's `ext`, pinned

`ext` is F7's to choose: the harness pre-sizes every array per input,
and three of the sizes are fixed by landed material — the CSR offset
zone (`hextOff`), the target zone (`hextTgt`) and the root renaming
(`hextUp`, `solveSpec_closed_scr`'s). Everything else the solve stages
allocate is theirs, so `f7ext` pins the three and defers the rest to a
parameter. The three lemmas below discharge the three hypotheses
outright, on **every** input, not merely the admissible ones. -/

/-- **F7's array sizing**: the two parse zones and the root renaming at
their landed lengths, every other name deferred. -/
def f7ext (rest : List ℕ → String → ℕ) (x : List ℕ) (a : String) : ℕ :=
  if a = "off" then vertexCount x + 1
  else if a = "tgt" then 2 * edgeCount x
  else if a = "up" then vertexCount x
  else rest x a

/-- `hextOff`, discharged. -/
@[simp] theorem f7ext_off (rest : List ℕ → String → ℕ) (x : List ℕ) :
    f7ext rest x "off" = vertexCount x + 1 := by simp [f7ext]

/-- `hextTgt`, discharged. -/
@[simp] theorem f7ext_tgt (rest : List ℕ → String → ℕ) (x : List ℕ) :
    f7ext rest x "tgt" = 2 * edgeCount x := by simp [f7ext]

/-- `hextUp` (`solveSpec_closed_scr`'s), discharged. -/
@[simp] theorem f7ext_up (rest : List ℕ → String → ℕ) (x : List ℕ) :
    f7ext rest x "up" = vertexCount x := by simp [f7ext]

/-- Every name the solve stages own is still the discharger's. -/
theorem f7ext_other (rest : List ℕ → String → ℕ) (x : List ℕ) {a : String}
    (h1 : a ≠ "off") (h2 : a ≠ "tgt") (h3 : a ≠ "up") :
    f7ext rest x a = rest x a := by simp [f7ext, h1, h2, h3]

/-! ## §1 The layout obstruction, witnessed -/

/-- `mcLayout` now carries the temporaries it is given, for every
extension. -/
theorem f7_mcLayout_temps (eS eA : List String) (t : ℕ) :
    (mcLayout eS eA t).temps = t := rfl

/-- **The obstruction, machine-checked**: three conjunctions nested on
the left compile to an expression that the old two-temporary layout
cannot host, whatever the extension lists and whatever the scatter
reads are. Since `verdictCom S av = .assign "verdict" (bcExpr av
(top S))` and `Com.Ok (.assign x e)` is `x ∈ L.scalars ∧ Expr.Ok L e 0`,
the pipeline's `hokS` failed at every sentence whose root combination
has this shape. Kept as the record of the defect the `temps` parameter
repairs; `SolveF7Temps.f7_bcExpr_ok_at_three` is the same expression
compiling at `t = 3`. -/
theorem f7_bcExpr_not_ok_at_mcLayout_two (eS eA : List String)
    (av : ScatterSentence 0 → Expr) :
    ¬ Expr.Ok (mcLayout eS eA 2)
      (bcExpr av (.and (.and (.and .tru .tru) .tru) .tru)) 0 := by
  simp [bcExpr, Expr.Ok, mcLayout]

/-! ## §2 The pipeline command, and its write discipline -/

open Classical in
/-- **The solve pipeline, named** — exactly the command
`SolveFrameBridge.solveSpec_closed_scr` concludes at. -/
noncomputable def mcSolveCom (S : Setup L) (frameBody : ℕ → Com → Com)
    (rootLoadCom scatCom : Com) (av : ScatterSentence L → Expr) (Kq : ℕ) : Com :=
  .seq matCom
    (.seq rootLoadCom
      (.seq (chainCom frameBody (canonBotB S Kq) S.depth 0)
        (topCom scatCom S av)))

open Classical in
/-- The pipeline compiles as soon as its three open pieces do — the
materialization is discharged here (`matCom_ok`), the rest is the name
bookkeeping `eS`/`eA` owe. -/
theorem mcSolveCom_ok {eS eA : List String} {t : ℕ} (S : Setup L)
    (frameBody : ℕ → Com → Com) (rootLoadCom scatCom : Com)
    (av : ScatterSentence L → Expr) (Kq : ℕ) (ht : 0 < t)
    (hk : "k" ∈ eS) (hup : "up" ∈ eA)
    (hrl : Com.Ok (mcLayout eS eA t) rootLoadCom)
    (hch : Com.Ok (mcLayout eS eA t) (chainCom frameBody (canonBotB S Kq) S.depth 0))
    (htp : Com.Ok (mcLayout eS eA t) (topCom scatCom S av)) :
    Com.Ok (mcLayout eS eA t) (mcSolveCom S frameBody rootLoadCom scatCom av Kq) :=
  ⟨matCom_ok ht hk hup, hrl, hch, htp⟩

open Classical in
/-- The pipeline never writes the output tape as soon as its three open
pieces do not — the epilogue's `writeScalar` is the only write, and it
is outside `solveCom` (`ProgCodegen.mcCom`). -/
theorem mcSolveCom_noWrite (S : Setup L) (frameBody : ℕ → Com → Com)
    (rootLoadCom scatCom : Com) (av : ScatterSentence L → Expr) (Kq : ℕ)
    (hrl : rootLoadCom.NoWrite)
    (hch : (chainCom frameBody (canonBotB S Kq) S.depth 0).NoWrite)
    (htp : (topCom scatCom S av).NoWrite) :
    (mcSolveCom S frameBody rootLoadCom scatCom av Kq).NoWrite :=
  ⟨matCom_noWrite, hrl, hch, htp⟩

/-! ## §3 The composition -/

open Classical in
/-- **The endorsed axiom, from `solveSpec_closed_scr`'s conclusion.**

`hclosed` is verbatim what `SolveFrameBridge.solveSpec_closed_scr`
produces, quantified over the axiom's `(n, G, w)`: the pipeline
`matCom ; rootLoadCom ; chainCom(frameBody, canonBotB) ; topCom`
satisfies `SolveSpec` at the graph-indexed budget
`matK x + (Krl x + (KBroot n G + (Kctop n G + topEvalCost S av)))`.
`KBroot n G` stands for `KB S.depth 0 (rootArena G (trivialColoring n))`,
and `Kctop n G` for the top scatter's own budget — **graph-indexed, not
a constant**: at the real stage it is `Θ(n + m)`, so hoisting it in
front of `n` and `G` (as an earlier version of this theorem did) is a
hypothesis no discharger can meet.

`hdom` is the uniformization F7 owes: one budget `Ks`, a function of
the word alone, above that graph-indexed one on every admissible input.
`hbr` then prices `Ks` against the charge ledger.

What remains after this theorem is exactly the three named residuals of
`SolveFrameBridge` (`FrameStepAllScr`, `RootLoadSpec`, `TopScatterAll`),
`solveSpec_closed_scr`'s own bookkeeping (of which `SolveF7CloseQ`
discharges `hB` and every constraint on `q`), the layout facts
`hokS`/`hnw`/`hextOff`/`hextTgt` — §1's `temps` obstruction is repaired,
and `SolveF7Temps` supplies the `t` at which `hokS`'s root-evaluation
half holds — and `hdom`/`hbr`. -/
theorem f7close_of_closed_scr
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (ε : ℝ) (hε : 0 < ε)
    (q c₀ Kq : ℕ) (Kctop : (m : ℕ) → SimpleGraph (Fin m) → ℕ)
    (eS eA : List String) (t : ℕ) (ext : List ℕ → String → ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (frameBody : ℕ → Com → Com) (rootLoadCom scatCom : Com)
    (av : ScatterSentence 0 → Expr) (Krl Ks : List ℕ → ℕ)
    (KBroot : (n : ℕ) → SimpleGraph (Fin n) → ℕ)
    (hq : 1 ≤ q) (ht : 2 ≤ t)
    (hokS : Com.Ok (mcLayout eS eA t)
      (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom scatCom
        av Kq))
    (hnw : (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom
      scatCom av Kq).NoWrite)
    (hextOff : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w, ext x "off" = vertexCount x + 1)
    (hextTgt : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w, ext x "tgt" = 2 * edgeCount x)
    (hclosed : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      SolveSpec C hC φ
        (selOrderingRoutine (fun m => bucketSel m)
          (3 * (Headline.headlineSetup C hC φ).R))
        G c₀ w q ext
        (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom
          scatCom av Kq)
        (fun x => matK x + (Krl x + (KBroot n G +
          (Kctop n G + topEvalCost (Headline.headlineSetup C hC φ) av)))))
    (hdom : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w,
        matK x + (Krl x + (KBroot n G +
          (Kctop n G + topEvalCost (Headline.headlineSetup C hC φ) av))) ≤ Ks x)
    (hbr : F7Bridge C hC φ ε ℓp htabF c₀ Ks) :
    ∃ (p : Lax13.Ram.Program) (c : ℕ) (T : List ℕ → ℕ),
      (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
        Lax13.RamComputes.ComputesInTime w p
          {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
          (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]) T :=
  f7close_exists_of_solveSpec C hC φ ε hε q c₀ eS eA t ext _ Ks ℓp htabF hq ht
    hokS hnw hextOff hextTgt
    (fun n G w hG =>
      f7_solveSpec_mono_Ks C hC φ _ G ext _ (hclosed n G w hG) (hdom n G w hG))
    hbr

open Classical in
/-- **The same, at F7's own `ext`** — `hextOff`/`hextTgt` are gone,
discharged by `f7ext`. What is left in the hypothesis list is the
pipeline's layout facts, `solveSpec_closed_scr`'s conclusion, the
uniformization `hdom`, and the ledger bridge. -/
theorem f7close_of_closed_scr_ext
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (ε : ℝ) (hε : 0 < ε)
    (q c₀ Kq : ℕ) (Kctop : (m : ℕ) → SimpleGraph (Fin m) → ℕ)
    (eS eA : List String) (t : ℕ) (rest : List ℕ → String → ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (frameBody : ℕ → Com → Com) (rootLoadCom scatCom : Com)
    (av : ScatterSentence 0 → Expr) (Krl Ks : List ℕ → ℕ)
    (KBroot : (n : ℕ) → SimpleGraph (Fin n) → ℕ)
    (hq : 1 ≤ q) (ht : 2 ≤ t)
    (hokS : Com.Ok (mcLayout eS eA t)
      (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom scatCom
        av Kq))
    (hnw : (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom
      scatCom av Kq).NoWrite)
    (hclosed : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      SolveSpec C hC φ
        (selOrderingRoutine (fun m => bucketSel m)
          (3 * (Headline.headlineSetup C hC φ).R))
        G c₀ w q (f7ext rest)
        (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom
          scatCom av Kq)
        (fun x => matK x + (Krl x + (KBroot n G +
          (Kctop n G + topEvalCost (Headline.headlineSetup C hC φ) av)))))
    (hdom : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w,
        matK x + (Krl x + (KBroot n G +
          (Kctop n G + topEvalCost (Headline.headlineSetup C hC φ) av))) ≤ Ks x)
    (hbr : F7Bridge C hC φ ε ℓp htabF c₀ Ks) :
    ∃ (p : Lax13.Ram.Program) (c : ℕ) (T : List ℕ → ℕ),
      (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
        Lax13.RamComputes.ComputesInTime w p
          {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
          (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]) T :=
  f7close_of_closed_scr C hC φ ε hε q c₀ Kq Kctop eS eA t (f7ext rest) ℓp htabF
    frameBody rootLoadCom scatCom av Krl Ks KBroot hq ht hokS hnw
    (fun _ _ _ _ x _ => f7ext_off rest x)
    (fun _ _ _ _ x _ => f7ext_tgt rest x)
    hclosed hdom hbr

/-! ## §5 The word decodes its own graph

The axiom's `T` — and with it every constant the close fixes — is
chosen before `n` and `G`, while the pipeline's budget mentions the
graph twice: the chain budget at the root arena, and the top scatter's
`Kc`, which at the real stage is `Θ(n + m)` and not a constant.  Both
are `ℕ`-valued functions of `(n, G)`, and `EncodesGraph` pins `(n, G)`
from the word: `n = vertexCount x`, and `adj_iff` reads the adjacency
off `x`'s own entries.  So a graph-indexed number *is* a function of the
word on the admissible set, and `f7Decode` is that function.

This is the residual `hdom` was standing in for — `f7Decode_eq` gives
it as an **equality**, so both directions are available: the `Spec`
side needs `graph-indexed ≤ Ks` and the bridge side needs
`Ks ≤ graph-indexed`, and a one-sided `hdom` can only ever supply one
of them. -/

/-- **An encoding determines the graph it encodes**, as far as any
`ℕ`-valued figure of it can tell: `vertexCount` pins the carrier and
`adj_iff` pins the adjacency, so two encodings of the same word give
the same number. -/
theorem f7_encodes_congr (Kg : (m : ℕ) → SimpleGraph (Fin m) → ℕ)
    {x : List ℕ} {n n' : ℕ} {G : SimpleGraph (Fin n)} {G' : SimpleGraph (Fin n')}
    (h : EncodesGraph x n G) (h' : EncodesGraph x n' G') : Kg n G = Kg n' G' := by
  have hn : n = n' := by rw [← h.vertexCount_eq, h'.vertexCount_eq]
  subst hn
  have : G = G' := by
    ext u v
    rw [h.adj_iff, h'.adj_iff]
  rw [this]

open Classical in
/-- **The graph-indexed figure, as a function of the word**: on a word
that encodes a graph, the figure of *that* graph; off the admissible
set, `0`. -/
noncomputable def f7Decode (Kg : (m : ℕ) → SimpleGraph (Fin m) → ℕ)
    (x : List ℕ) : ℕ :=
  if h : ∃ (m : ℕ) (H : SimpleGraph (Fin m)), EncodesGraph x m H then
    Kg h.choose h.choose_spec.choose
  else 0

open Classical in
/-- **The decoding is exact on encodings** — an equality, not a bound,
so it serves the `Spec` side and the bridge side at once. -/
theorem f7Decode_eq (Kg : (m : ℕ) → SimpleGraph (Fin m) → ℕ) {x : List ℕ}
    {n : ℕ} {G : SimpleGraph (Fin n)} (h : EncodesGraph x n G) :
    f7Decode Kg x = Kg n G := by
  have hex : ∃ (m : ℕ) (H : SimpleGraph (Fin m)), EncodesGraph x m H := ⟨n, G, h⟩
  rw [f7Decode, dif_pos hex]
  exact f7_encodes_congr Kg hex.choose_spec.choose_spec h

/-- **The uniform solve budget**: the pipeline's own budget with its two
graph-indexed summands decoded from the word.  A `List ℕ → ℕ`, fixed
with the rest of the program data before `n` and `G` — which is what the
axiom's binder order demands of `Ks`. -/
noncomputable def f7Ks (Krl : List ℕ → ℕ)
    (KBroot Kctop : (m : ℕ) → SimpleGraph (Fin m) → ℕ) (Ktop : ℕ)
    (x : List ℕ) : ℕ :=
  matK x + (Krl x + (f7Decode KBroot x + (f7Decode Kctop x + Ktop)))

/-- `f7Ks` **is** the graph-indexed budget on every admissible input —
the equality that replaces `hdom`. -/
theorem f7Ks_eq (Krl : List ℕ → ℕ)
    (KBroot Kctop : (m : ℕ) → SimpleGraph (Fin m) → ℕ) (Ktop : ℕ)
    {n : ℕ} {G : SimpleGraph (Fin n)} {c₀ w : ℕ} {x : List ℕ}
    (hx : x ∈ mcD n G c₀ w) :
    f7Ks Krl KBroot Kctop Ktop x
      = matK x + (Krl x + (KBroot n G + (Kctop n G + Ktop))) := by
  rw [f7Ks, f7Decode_eq KBroot hx.1, f7Decode_eq Kctop hx.1]

/-! ## §6 `F7Bridge`, discharged

`SolveF7Close.F7Bridge` is `SolveChain.KsChargeBridge` with `∃ cB`
pulled out in front of `n`, `G` and `w`, and with the cover family's own
constant `cf` universally quantified.  Both moves are forced by the
axiom's binder order, and both cost something concrete:

* **the constant.**  `b7Cb`'s internal figures (`b7M`, `b7BotA`/
  `b7BotB`, `b7Cen`, `b7EdgeC`/`b7ScatC`, `b7BotK`, `topEvalCost`) take
  no carrier and no arena — their *types* say so — so they are uniform
  as they stand.  The two stage budgets are not: `Krl x` is `Θ(|x|)` and
  the top scatter's `Kc` is `Θ(n + m)`.  `SolveF7Bridge` now asks for
  both at a *rate* (`hKrl`, `hKc`) and puts the rates `crl`, `ckc` in
  the constant, which is what makes `b7Cb` schedule-only.
* **the cover constant.**  The landed cover column holds at the `cf₀`
  `exists_mcChargeMS_T_bucket_coverColumn` produces and at no smaller
  one.  `SolveF7BridgeCover` §3 shows the column moves by at most the
  schedule factor `⌈cf₀⌉₊` between any two `cf ≥ 1`, so `ccov` is taken
  `⌈cf₀⌉₊·(a+b+c)` once and the `∀ cf` is met.

* **the budget.**  `Ks` must be a function of the word, while the
  pipeline's budget names the graph twice.  §5's `f7Decode` supplies the
  missing direction. -/

open Classical in
/-- **`F7Bridge`, discharged at the machine's own cover routine, peel
budget and glue contract** — the constant exhibited, fixed before `n`
and `G`, and good at every `cf ≥ 1`.

`hKrl` is the root load's rate (a residual of `RootLoadSpec`) and `hKc`
the top scatter's (a residual of `TopScatterAll`); nothing else is
assumed. -/
theorem f7_bridge_bucket (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) (Kq a b cc c₀ : ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (Krl : List ℕ → ℕ) (Kctop : (m : ℕ) → SimpleGraph (Fin m) → ℕ)
    (crl ckc : ℕ) (av : ScatterSentence 0 → Expr)
    (hKrl : ∀ x : List ℕ, Krl x ≤ crl * (x.length + 1))
    (hKc : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w, Kctop n G ≤ ckc * (x.length + 1)) :
    F7Bridge C hC φ ε ℓp htabF c₀
      (f7Ks Krl
        (fun n G => chainKB (Headline.headlineSetup C hC φ)
          (selOrderingRoutine (fun m => bucketSel m)
            (3 * (Headline.headlineSetup C hC φ).R)) Kq ℓp
          (fun _ => 2 * (Headline.headlineSetup C hC φ).R + 1)
          (fun _ A => peelK a b cc (Headline.headlineSetup C hC φ) A
            ((selOrderingRoutine (fun m => bucketSel m)
                (3 * (Headline.headlineSetup C hC φ).R)) A.N A.G).order)
          (fun _ _ _ => 6) (Headline.headlineSetup C hC φ).depth 0
          (rootArena G (Impl.trivialColoring n)))
        Kctop (topEvalCost (Headline.headlineSetup C hC φ) av)) := by
  classical
  have hδ : 0 < headlineδ (Headline.headlineSetup C hC φ) ε := by
    unfold headlineδ; positivity
  obtain ⟨cf₀, -, -, hcf₀, -, -, -, hcol⟩ :=
    exists_mcChargeMS_T_bucket_coverColumn C hC φ hε ℓp
  have h1K : 1 ≤ ⌈cf₀⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  refine ⟨b7Cb (Headline.headlineSetup C hC φ) ℓp
    (b7BotK (Headline.headlineSetup C hC φ) Kq) (⌈cf₀⌉₊ * (a + b + cc)) 6
    crl ckc av, ?_⟩
  intro cf hcf n G w hG x hx
  rw [f7Ks_eq (c₀ := c₀) (w := w) _ _ _ _ hx]
  refine b7_Ks_le C hC φ _ G c₀ w Kq ℓp _ (htabF n) _ _ _ Krl (Kctop n G) av
    (b7BotK (Headline.headlineSetup C hC φ) Kq) (⌈cf₀⌉₊ * (a + b + cc)) 6 crl ckc
    (chainAdm (Headline.headlineSetup C hC φ) G)
    (headlineSetup_chainAdm_root C hC φ G)
    (headlineSetup_chainAdm_admChild C hC φ _ G)
    (fun _ => rfl)
    (b7_botK_le (Headline.headlineSetup C hC φ) Kq)
    (fun i A hi hAdm hbot => ?_) (fun i A hbot => ?_)
    (fun k i A => by omega) (fun y _ => hKrl y)
    (fun y hy => hKc n G w hG y hy) x hx
  · calc peelK a b cc (Headline.headlineSetup C hC φ) A _
        ≤ (a + b + cc) * chargeTotal (coverCFSel (fun m => bucketSel m)
            (Headline.headlineSetup C hC φ) cf₀
            (headlineδ (Headline.headlineSetup C hC φ) ε) i A) :=
          hcol n G hG i A (ardIsContained_of_chainAdm hi hAdm hbot) a b cc
      _ ≤ (a + b + cc) * (⌈cf₀⌉₊ * chargeTotal (coverCFSel (fun m => bucketSel m)
            (Headline.headlineSetup C hC φ) cf
            (headlineδ (Headline.headlineSetup C hC φ) ε) i A)) :=
          Nat.mul_le_mul_left _ (b7c_chargeTotal_coverCFSel_le_mul
            (fun m => bucketSel m) (Headline.headlineSetup C hC φ)
            hcf₀ hcf hδ.le i A)
      _ = ⌈cf₀⌉₊ * (a + b + cc) * chargeTotal (coverCFSel (fun m => bucketSel m)
            (Headline.headlineSetup C hC φ) cf
            (headlineδ (Headline.headlineSetup C hC φ) ε) i A) := by ring
      _ ≤ ⌈cf₀⌉₊ * (a + b + cc) * (chargeTotal (coverCFSel (fun m => bucketSel m)
            (Headline.headlineSetup C hC φ) cf
            (headlineδ (Headline.headlineSetup C hC φ) ε) i A) + A.N + 1) :=
          Nat.mul_le_mul_left _ (by omega)
  · exact le_trans (b7c_peelK_le_bot a b cc _ A _ hbot)
      (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega)))

/-! ## §7 The endorsed axiom, from the three named residuals

Everything F7-c owed is now spent.  `f7close_of_closed_scr_bucket`
takes `SolveFrameBridge.solveSpec_closed_scr`'s conclusion at the
machine's own cover routine, peel budget and glue contract, and returns
the endorsed axiom's `∃ p c T`.  What is left standing in its hypothesis
list is exactly:

* `hclosed` — `solveSpec_closed_scr` applied per `(n, G, w)`, i.e. the
  three named residuals `FrameStepAllScr`, `RootLoadSpec`,
  `TopScatterAll` and that theorem's own bookkeeping;
* `hKrl` / `hKc` — the two stage budgets at a rate: `Krl x ≤ crl·(|x|+1)`
  and `Kctop n G ≤ ckc·(|x|+1)` on admissible inputs.  The first is a
  clause of `RootLoadSpec`'s cost column, the second of
  `TopScatterAll`'s;
* `hokS` / `hnw` — the pipeline compiles and never writes the tape;
  `SolveF7Temps` supplies the layout depth and discharges the
  materialization's and the root evaluation's halves of `hokS`.

`hdom` is **gone**: §5's decoding proves it, as an equality. -/

open Classical in
/-- **The endorsed axiom, from `solveSpec_closed_scr` at the machine's
own cover column.**  The uniform budget is `f7Ks` — the pipeline's own
budget with its two graph-indexed summands decoded from the word — so
the `SolveSpec` side and the ledger side see the same number, and the
ledger bridge is `f7_bridge_bucket`. -/
theorem f7close_of_closed_scr_bucket
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (ε : ℝ) (hε : 0 < ε)
    (q c₀ Kq a b cc : ℕ) (eS eA : List String) (t : ℕ)
    (rest : List ℕ → String → ℕ) (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (frameBody : ℕ → Com → Com) (rootLoadCom scatCom : Com)
    (av : ScatterSentence 0 → Expr) (Krl : List ℕ → ℕ)
    (Kctop : (m : ℕ) → SimpleGraph (Fin m) → ℕ) (crl ckc : ℕ)
    (hq : 1 ≤ q) (ht : 2 ≤ t)
    (hokS : Com.Ok (mcLayout eS eA t)
      (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom scatCom
        av Kq))
    (hnw : (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom
      scatCom av Kq).NoWrite)
    (hKrl : ∀ x : List ℕ, Krl x ≤ crl * (x.length + 1))
    (hKc : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w, Kctop n G ≤ ckc * (x.length + 1))
    (hclosed : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      SolveSpec C hC φ
        (selOrderingRoutine (fun m => bucketSel m)
          (3 * (Headline.headlineSetup C hC φ).R))
        G c₀ w q (f7ext rest)
        (mcSolveCom (Headline.headlineSetup C hC φ) frameBody rootLoadCom
          scatCom av Kq)
        (fun x => matK x + (Krl x +
          (chainKB (Headline.headlineSetup C hC φ)
            (selOrderingRoutine (fun m => bucketSel m)
              (3 * (Headline.headlineSetup C hC φ).R)) Kq ℓp
            (fun _ => 2 * (Headline.headlineSetup C hC φ).R + 1)
            (fun _ A => peelK a b cc (Headline.headlineSetup C hC φ) A
              ((selOrderingRoutine (fun m => bucketSel m)
                  (3 * (Headline.headlineSetup C hC φ).R)) A.N A.G).order)
            (fun _ _ _ => 6) (Headline.headlineSetup C hC φ).depth 0
            (rootArena G (Impl.trivialColoring n)) +
            (Kctop n G + topEvalCost (Headline.headlineSetup C hC φ) av))))) :
    ∃ (p : Lax13.Ram.Program) (c : ℕ) (T : List ℕ → ℕ),
      (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
        Lax13.RamComputes.ComputesInTime w p
          {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
          (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]) T :=
  f7close_of_closed_scr_ext C hC φ ε hε q c₀ Kq Kctop eS eA t rest ℓp htabF
    frameBody rootLoadCom scatCom av Krl
    (f7Ks Krl (fun n G => chainKB (Headline.headlineSetup C hC φ)
          (selOrderingRoutine (fun m => bucketSel m)
            (3 * (Headline.headlineSetup C hC φ).R)) Kq ℓp
          (fun _ => 2 * (Headline.headlineSetup C hC φ).R + 1)
          (fun _ A => peelK a b cc (Headline.headlineSetup C hC φ) A
            ((selOrderingRoutine (fun m => bucketSel m)
                (3 * (Headline.headlineSetup C hC φ).R)) A.N A.G).order)
          (fun _ _ _ => 6) (Headline.headlineSetup C hC φ).depth 0
          (rootArena G (Impl.trivialColoring n))) Kctop (topEvalCost (Headline.headlineSetup C hC φ) av))
    (fun n G => chainKB (Headline.headlineSetup C hC φ)
          (selOrderingRoutine (fun m => bucketSel m)
            (3 * (Headline.headlineSetup C hC φ).R)) Kq ℓp
          (fun _ => 2 * (Headline.headlineSetup C hC φ).R + 1)
          (fun _ A => peelK a b cc (Headline.headlineSetup C hC φ) A
            ((selOrderingRoutine (fun m => bucketSel m)
                (3 * (Headline.headlineSetup C hC φ).R)) A.N A.G).order)
          (fun _ _ _ => 6) (Headline.headlineSetup C hC φ).depth 0
          (rootArena G (Impl.trivialColoring n))) hq ht hokS hnw hclosed
    (fun n G w _ x hx => le_of_eq
      (f7Ks_eq Krl (fun n G => chainKB (Headline.headlineSetup C hC φ)
          (selOrderingRoutine (fun m => bucketSel m)
            (3 * (Headline.headlineSetup C hC φ).R)) Kq ℓp
          (fun _ => 2 * (Headline.headlineSetup C hC φ).R + 1)
          (fun _ A => peelK a b cc (Headline.headlineSetup C hC φ) A
            ((selOrderingRoutine (fun m => bucketSel m)
                (3 * (Headline.headlineSetup C hC φ).R)) A.N A.G).order)
          (fun _ _ _ => 6) (Headline.headlineSetup C hC φ).depth 0
          (rootArena G (Impl.trivialColoring n))) Kctop
        (topEvalCost (Headline.headlineSetup C hC φ) av) hx).symm)
    (f7_bridge_bucket C hC φ hε ℓp Kq a b cc c₀ htabF Krl Kctop crl ckc av
      hKrl hKc)

/-! ## §8 The leaf's axiom profile -/

#print axioms f7ext_off

#print axioms f7ext_tgt

#print axioms f7ext_up

#print axioms f7_mcLayout_temps

#print axioms f7_bcExpr_not_ok_at_mcLayout_two

#print axioms mcSolveCom_ok

#print axioms mcSolveCom_noWrite

#print axioms f7close_of_closed_scr

#print axioms f7_encodes_congr

#print axioms f7Decode_eq

#print axioms f7Ks_eq

#print axioms f7_bridge_bucket

#print axioms f7close_of_closed_scr_ext

#print axioms f7close_of_closed_scr_bucket

end Lax3Proofs.Prog
