import Lax3Proofs.SolveF7CloseQ

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

## §1 The layout obstruction (**not** repaired here — a finding)

`ProgCodegenLayout.mcLayout eS eA` fixes `temps = 2`
(`f7_mcLayout_temps`). `Lax13Proofs.Compile.Expr.Ok` charges one
temporary per level of *left* nesting: `Expr.Ok L (.bin _ e f) d` asks
for `Expr.Ok L e (d+1)` and `d < L.temps`. The root evaluation compiles
the sentence's boolean combination into one expression —
`SolveMatTop.verdictCom S av = .assign "verdict" (bcExpr av (top S))`,
and `bcExpr` sends `.and b c` to `.mul (bcExpr av b) (bcExpr av c)`,
nesting **left**. So a combination with three nested conjunctions on
the left already needs `temps ≥ 3`, and `f7_bcExpr_not_ok_at_mcLayout`
exhibits one that does not compile at `mcLayout`'s two.

`ProgCodegen.mc_computesInTime_of_solveSpec`'s hypothesis
`hokS : Com.Ok (mcLayout eS eA) solveCom` is therefore **unsatisfiable
for the real pipeline** at every sentence whose root combination nests
three conjunctions on the left — which is most of them. This is not a
gap in the assembly: both `ProgCodegenLayout`'s docstring ("a bigger
`temps` only shifts the constant in `hspan`") and `SolveMatTop`'s
layout note ("F7 instantiates the layout with `temps ≥` the compiled
combination's depth") say F7 should raise `temps` — but `mcLayout` has
no `temps` argument to raise. The repair is one parameter on a landed
definition, and it is small and mechanical:

* `mcLayout eS eA t := ⟨parseScalars ++ eS, ["off","tgt"] ++ eA, t⟩`;
* `mcLayout_span_le`/`mcLayout_fitsWords`'s `hspan` becomes
  `9 + t + |eS| + (2 + |eA|)·q ≤ c` (the literal `11` is `2 + 9`, the
  fixed `temps` plus the nine parse scalars);
* `parseCom_ok` needs `2 ≤ t`, and `mcCom_ok`'s epilogue `0 < t`;
* every downstream mention of `mcLayout eS eA` gains the argument.

Nothing else in the tower depends on `temps` — `Layout.const` is
`3·idxLen + 13` and `idxLen` counts *arrays*, so the machine constant is
untouched, and the axiom's `c` absorbs the span exactly as before.
Because `mcLayout` is landed, this file does not make the change; it
records the obstruction with a machine-checked witness so the supervisor
can land the parameter in `ProgCodegenLayout`/`ProgCodegen`. Everything
else in F7-c is independent of it: the close, the constants and the time
bound are all stated against `mcLayout eS eA` and transport verbatim to
the `temps`-parametric version.
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

/-- `mcLayout` fixes two temporaries, for every extension. -/
theorem f7_mcLayout_temps (eS eA : List String) : (mcLayout eS eA).temps = 2 := rfl

/-- **The obstruction, machine-checked**: three conjunctions nested on
the left compile to an expression that `mcLayout` cannot host, whatever
the extension lists and whatever the scatter reads are. Since
`verdictCom S av = .assign "verdict" (bcExpr av (top S))` and
`Com.Ok (.assign x e)` is `x ∈ L.scalars ∧ Expr.Ok L e 0`, the
pipeline's `hokS` fails at every sentence whose root combination has
this shape. -/
theorem f7_bcExpr_not_ok_at_mcLayout (eS eA : List String)
    (av : ScatterSentence 0 → Expr) :
    ¬ Expr.Ok (mcLayout eS eA)
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
theorem mcSolveCom_ok {eS eA : List String} (S : Setup L)
    (frameBody : ℕ → Com → Com) (rootLoadCom scatCom : Com)
    (av : ScatterSentence L → Expr) (Kq : ℕ)
    (hk : "k" ∈ eS) (hup : "up" ∈ eA)
    (hrl : Com.Ok (mcLayout eS eA) rootLoadCom)
    (hch : Com.Ok (mcLayout eS eA) (chainCom frameBody (canonBotB S Kq) S.depth 0))
    (htp : Com.Ok (mcLayout eS eA) (topCom scatCom S av)) :
    Com.Ok (mcLayout eS eA) (mcSolveCom S frameBody rootLoadCom scatCom av Kq) :=
  ⟨matCom_ok hk hup, hrl, hch, htp⟩

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
`matK x + (Krl x + (KBroot n G + (Kc + topEvalCost S av)))`. `KBroot n G`
stands for `KB S.depth 0 (rootArena G (trivialColoring n))`.

`hdom` is the uniformization F7 owes: one budget `Ks`, a function of
the word alone, above that graph-indexed one on every admissible input.
`hbr` then prices `Ks` against the charge ledger.

What remains after this theorem is exactly the three named residuals of
`SolveFrameBridge` (`FrameStepAllScr`, `RootLoadSpec`, `TopScatterAll`),
`solveSpec_closed_scr`'s own bookkeeping (of which `SolveF7CloseQ`
discharges `hB` and every constraint on `q`), the layout facts
`hokS`/`hnw`/`hextOff`/`hextTgt` — subject to §1's `temps` obstruction —
and `hdom`/`hbr`. -/
theorem f7close_of_closed_scr
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (ε : ℝ) (hε : 0 < ε)
    (q c₀ Kq Kc : ℕ) (eS eA : List String) (ext : List ℕ → String → ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (frameBody : ℕ → Com → Com) (rootLoadCom scatCom : Com)
    (av : ScatterSentence 0 → Expr) (Krl Ks : List ℕ → ℕ)
    (KBroot : (n : ℕ) → SimpleGraph (Fin n) → ℕ)
    (hq : 1 ≤ q)
    (hokS : Com.Ok (mcLayout eS eA)
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
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))))
    (hdom : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w,
        matK x + (Krl x + (KBroot n G +
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av))) ≤ Ks x)
    (hbr : F7Bridge C hC φ ε ℓp htabF c₀ Ks) :
    ∃ (p : Lax13.Ram.Program) (c : ℕ) (T : List ℕ → ℕ),
      (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
        Lax13.RamComputes.ComputesInTime w p
          {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
          (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]) T :=
  f7close_exists_of_solveSpec C hC φ ε hε q c₀ eS eA ext _ Ks ℓp htabF hq
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
    (q c₀ Kq Kc : ℕ) (eS eA : List String) (rest : List ℕ → String → ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (frameBody : ℕ → Com → Com) (rootLoadCom scatCom : Com)
    (av : ScatterSentence 0 → Expr) (Krl Ks : List ℕ → ℕ)
    (KBroot : (n : ℕ) → SimpleGraph (Fin n) → ℕ)
    (hq : 1 ≤ q)
    (hokS : Com.Ok (mcLayout eS eA)
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
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av)))))
    (hdom : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w,
        matK x + (Krl x + (KBroot n G +
          (Kc + topEvalCost (Headline.headlineSetup C hC φ) av))) ≤ Ks x)
    (hbr : F7Bridge C hC φ ε ℓp htabF c₀ Ks) :
    ∃ (p : Lax13.Ram.Program) (c : ℕ) (T : List ℕ → ℕ),
      (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
        Lax13.RamComputes.ComputesInTime w p
          {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
          (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]) T :=
  f7close_of_closed_scr C hC φ ε hε q c₀ Kq Kc eS eA (f7ext rest) ℓp htabF
    frameBody rootLoadCom scatCom av Krl Ks KBroot hq hokS hnw
    (fun _ _ _ _ x _ => f7ext_off rest x)
    (fun _ _ _ _ x _ => f7ext_tgt rest x)
    hclosed hdom hbr

/-! ## §4 The leaf's axiom profile -/

#print axioms f7ext_off

#print axioms f7ext_tgt

#print axioms f7ext_up

#print axioms f7_mcLayout_temps

#print axioms f7_bcExpr_not_ok_at_mcLayout

#print axioms mcSolveCom_ok

#print axioms mcSolveCom_noWrite

#print axioms f7close_of_closed_scr

#print axioms f7close_of_closed_scr_ext

end Lax3Proofs.Prog
