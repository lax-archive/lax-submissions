import Lax3Proofs.SolveF7CloseCompose
import Lax3Proofs.SolveSeamTop

/-!
# F7-c, part 4 — the layout's temporaries: how many, and why the number
is a constant of the schedule

`SolveF7CloseCompose` §1 recorded the defect: `mcLayout` fixed
`temps = 2`, `Expr.Ok` charges one temporary per level of **left**
nesting, and the root evaluation folds the sentence's whole boolean
combination into one left-nested expression, so
`ProgCodegen.mc_computesInTime_of_solveSpec`'s `hokS` was unsatisfiable
for the real pipeline. `ProgCodegenLayout` now takes the temporaries as
a parameter. This file answers the question that parameter raises:

> at **which** `t` does `hokS` hold, and is that `t` fixed before the
> input?

## The answer

`exprTemps` (`ProgCodegenLayout` §0) counts the temporaries an
expression needs, as a function of the expression alone. The number the
root evaluation needs is therefore

    f7Temps S av = max 2 (exprTemps (bcExpr av (top S))),

whose type is `Setup L → (ScatterSentence L → Expr) → ℕ` — **no
carrier, no graph, no word**. The schedule `S` and the block family's
read expressions `av` are both fixed with `eS`, `eA` and the rest of the
program data, before `n`, `G` and `x`, so `f7Temps S av` is fixed there
too. That is the whole of the uniformity claim, and it is carried by the
type rather than asserted.

§1 makes it structural as well: `bcHeight` is the left-nesting height of
a boolean combination, and

    exprTemps (bcExpr av b) ≤ M + bcHeight b     whenever
      every read `av σa` needs at most `M`,

so the layout's depth is *the sentence's own nesting height plus the
depth of the block family's read expressions*, and nothing else. The
sentence is `top S` — a finite term produced by `localityBC` from
`(C, φ)` — so its height is a schedule figure, and `av`'s depths are the
descent's own, fixed with the command it compiles.

## What this costs

Nothing at the cost level and one unit of the axiom's constant per
temporary at the layout level:

* `Layout.const = 3·idxLen + 13` counts **arrays** — `mcLayout_const_eq`
  proves the machine constant is literally the same at every `t`, so the
  headline exponent `1 + ε` and the time bound are untouched;
* `hspan` becomes `9 + t + |eS| + (2+|eA|)·q ≤ c`, and `c` is chosen
  after everything (`SolveF7Close`'s `f7c`), so raising `t` is absorbed
  by one `omega` step.

## Anti-vacuity

`f7_bcExpr_ok_at_three` compiles, at `t = 3`, the very expression
`SolveF7CloseCompose.f7_bcExpr_not_ok_at_mcLayout_two` shows does not
compile at `t = 2` — the same term, the same layout family, opposite
verdicts. `verdictCom_ok_f7Temps` then discharges the root evaluation's
half of `hokS` outright, with the block family's read *names* as the
only hypothesis (their depths are already paid for by `f7Temps`).

## §6, and why it lives here

`SolveF7CloseCompose.f7_bridge_bucket` asks the top scatter's budget at
a *rate* — `Kctop n G ≤ ckc·(|x|+1)` — because that budget is `Θ(n+m)`
and the bridge's constant is fixed before `n` and `G`. §6 proves the
rate exists and exhibits it: `f7ScatRate atoms`, a function of the
schedule's scatter atoms alone. It needs `SolveSeamTop`'s `topScatK`,
which no file on the composition's import path reaches; putting the
import on this leaf keeps the new edge out of the shared files (and out
of the way of the concurrent work on that seam).
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Compile
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax3Proofs.Driver

variable {L : ℕ}

/-! ## §1 The left-nesting height of a boolean combination -/

/-- **The left-nesting height** of a boolean combination — the number of
temporaries `bcExpr` spends on the combination's own structure.
Conjunction is the only constructor that deepens, and it deepens on the
**left**, because `bcExpr (.and b c) = .mul (bcExpr av b) (bcExpr av c)`
and `Expr.Ok L (.bin _ e f) d` recurses into `e` at `d+1`. Negation
costs one temporary but never nests. -/
def bcHeight {α : Type*} : BC α → ℕ
  | .atom _ => 0
  | .tru => 0
  | .not b => max (bcHeight b) 1
  | .and b c => max (bcHeight c) (bcHeight b + 1)

@[simp] theorem bcHeight_atom {α : Type*} (a : α) :
    bcHeight (BC.atom a) = 0 := rfl

@[simp] theorem bcHeight_tru {α : Type*} : bcHeight (BC.tru (α := α)) = 0 := rfl

@[simp] theorem bcHeight_not {α : Type*} (b : BC α) :
    bcHeight b.not = max (bcHeight b) 1 := rfl

@[simp] theorem bcHeight_and {α : Type*} (b c : BC α) :
    bcHeight (b.and c) = max (bcHeight c) (bcHeight b + 1) := rfl

open Classical in
/-- **The compiled combination's depth, bounded by the schedule**: the
sentence's own left-nesting height plus whatever the block family's read
expressions need. Both summands are fixed before the input — `b` is a
term of the schedule and `M` a figure of the compiled reads — so this is
the statement that the layout's `temps` can be chosen before `n`, `G`
and `x`. -/
theorem exprTemps_bcExpr_le {av : ScatterSentence L → Expr} {M : ℕ}
    (hav : ∀ σa, exprTemps (av σa) ≤ M) :
    ∀ b : BC (DistFO L 0 ⊕ ScatterSentence L),
      exprTemps (bcExpr av b) ≤ M + bcHeight b := by
  intro b
  induction b with
  | atom a =>
    rcases a with ψ | σa
    · simp [bcExpr]
    · simpa [bcExpr] using hav σa
  | tru => simp [bcExpr]
  | not b ih =>
    rw [bcExpr, Expr.sub_def, exprTemps_bin, exprTemps_lit, bcHeight_not]
    omega
  | and b c ihb ihc =>
    rw [bcExpr, Expr.mul_def, exprTemps_bin, bcHeight_and]
    omega

/-! ## §2 The layout depth the root evaluation needs -/

open Classical in
/-- **The temporaries the pipeline's layout must carry**: two for the
front end's array scans, and whatever the compiled root combination
needs. A function of the schedule and the block family's read
expressions — its type mentions no carrier, no graph and no word, which
is exactly the uniformity `ProgCodegen`'s binder order requires of every
piece of program data. -/
noncomputable def f7Temps (S : Setup L) (av : ScatterSentence L → Expr) : ℕ :=
  max 2 (exprTemps (bcExpr av (top S)))

theorem two_le_f7Temps (S : Setup L) (av : ScatterSentence L → Expr) :
    2 ≤ f7Temps S av := le_max_left _ _

theorem exprTemps_le_f7Temps (S : Setup L) (av : ScatterSentence L → Expr) :
    exprTemps (bcExpr av (top S)) ≤ f7Temps S av := le_max_right _ _

open Classical in
/-- **The schedule bound on the layout depth**, structurally: the
sentence's left-nesting height plus the reads' own depth. -/
theorem f7Temps_le (S : Setup L) {av : ScatterSentence L → Expr} {M : ℕ}
    (hav : ∀ σa, exprTemps (av σa) ≤ M) :
    f7Temps S av ≤ max 2 (M + bcHeight (top S)) :=
  max_le_max le_rfl (exprTemps_bcExpr_le hav (top S))

/-! ## §3 The root evaluation compiles -/

/-- The names a compiled combination mentions are the reads' names — the
`localConst` atoms compile to literals and the connectives introduce
none. -/
theorem bcExpr_namesOk {Lay : Layout} {av : ScatterSentence L → Expr}
    (hav : ∀ σa, ExprNamesOk Lay (av σa)) :
    ∀ b : BC (DistFO L 0 ⊕ ScatterSentence L), ExprNamesOk Lay (bcExpr av b) := by
  intro b
  induction b with
  | atom a =>
    rcases a with ψ | σa
    · simp [bcExpr, ExprNamesOk]
    · simpa [bcExpr] using hav σa
  | tru => simp [bcExpr, ExprNamesOk]
  | not b ih =>
    rw [bcExpr, Expr.sub_def]
    exact ⟨trivial, ih⟩
  | and b c ihb ihc =>
    rw [bcExpr, Expr.mul_def]
    exact ⟨ihb, ihc⟩

open Classical in
/-- **The verdict assignment compiles**, at any layout deep enough for
the compiled combination. The only hypothesis is the block family's
read *names*: their depths are already accounted for by `ht`. -/
theorem verdictCom_ok {eS eA : List String} {t : ℕ} (S : Setup L)
    (av : ScatterSentence L → Expr)
    (hav : ∀ σa, ExprNamesOk (mcLayout eS eA t) (av σa))
    (ht : exprTemps (bcExpr av (top S)) ≤ t) :
    Com.Ok (mcLayout eS eA t) (verdictCom S av) := by
  refine ⟨mcLayout_verdict_mem eS eA t, ?_⟩
  exact expr_ok_of_exprTemps _ 0 (bcExpr_namesOk hav (top S)) (by simpa using ht)

open Classical in
/-- **The root evaluation's half of `hokS`, discharged at `f7Temps`** —
the `t` the pipeline needs, exhibited. -/
theorem verdictCom_ok_f7Temps {eS eA : List String} (S : Setup L)
    (av : ScatterSentence L → Expr)
    (hav : ∀ σa, ExprNamesOk (mcLayout eS eA (f7Temps S av)) (av σa)) :
    Com.Ok (mcLayout eS eA (f7Temps S av)) (verdictCom S av) :=
  verdictCom_ok S av hav (exprTemps_le_f7Temps S av)

open Classical in
/-- The composed root evaluation compiles as soon as the block family's
scatter stage does. -/
theorem topCom_ok {eS eA : List String} {t : ℕ} (S : Setup L) {scatCom : Com}
    (av : ScatterSentence L → Expr)
    (hsc : Com.Ok (mcLayout eS eA t) scatCom)
    (hav : ∀ σa, ExprNamesOk (mcLayout eS eA t) (av σa))
    (ht : exprTemps (bcExpr av (top S)) ≤ t) :
    Com.Ok (mcLayout eS eA t) (topCom scatCom S av) :=
  ⟨hsc, verdictCom_ok S av hav ht⟩

open Classical in
/-- **The whole solve pipeline compiles**, at `t = f7Temps S av`, with
the two *parameter* stages (`rootLoadCom`, the chain) as the only open
compilability facts left — the materialization and the root evaluation
are discharged here. This is `ProgCodegen`'s `hokS` for the real
pipeline, at a `t` fixed before the input. -/
theorem mcSolveCom_ok_f7Temps {eS eA : List String} (S : Setup L)
    (frameBody : ℕ → Com → Com) (rootLoadCom scatCom : Com)
    (av : ScatterSentence L → Expr) (Kq : ℕ)
    (hk : "k" ∈ eS) (hup : "up" ∈ eA)
    (hrl : Com.Ok (mcLayout eS eA (f7Temps S av)) rootLoadCom)
    (hch : Com.Ok (mcLayout eS eA (f7Temps S av))
      (chainCom frameBody (canonBotB S Kq) S.depth 0))
    (hsc : Com.Ok (mcLayout eS eA (f7Temps S av)) scatCom)
    (hav : ∀ σa, ExprNamesOk (mcLayout eS eA (f7Temps S av)) (av σa)) :
    Com.Ok (mcLayout eS eA (f7Temps S av))
      (mcSolveCom S frameBody rootLoadCom scatCom av Kq) :=
  mcSolveCom_ok S frameBody rootLoadCom scatCom av Kq
    (by have := two_le_f7Temps S av; omega) hk hup hrl hch
    (topCom_ok S av hsc hav (exprTemps_le_f7Temps S av))

/-! ## §4 Anti-vacuity: the witness that failed at two, compiling at three -/

/-- **The positive counterpart of the obstruction.** The very expression
`SolveF7CloseCompose.f7_bcExpr_not_ok_at_mcLayout_two` refutes at
`t = 2` compiles at `t = 3` — same term, same layout family, opposite
verdicts. So the `temps` parameter is not a formality: it is what turns
`hokS` from unsatisfiable into satisfiable. -/
theorem f7_bcExpr_ok_at_three (eS eA : List String)
    (av : ScatterSentence 0 → Expr) :
    Expr.Ok (mcLayout eS eA 3)
      (bcExpr av (.and (.and (.and .tru .tru) .tru) .tru)) 0 := by
  simp [bcExpr, Expr.Ok, mcLayout]

/-- The same witness, priced by `exprTemps`: three, on the nose. -/
theorem f7_exprTemps_witness (av : ScatterSentence 0 → Expr) :
    exprTemps (bcExpr av (.and (.and (.and .tru .tru) .tru) .tru)) = 3 := by
  simp [bcExpr, exprTemps]

/-- And its left-nesting height is three too — the bound of §1 is tight
on the witness. -/
theorem f7_bcHeight_witness :
    bcHeight (α := DistFO 0 0 ⊕ ScatterSentence 0)
      (.and (.and (.and .tru .tru) .tru) .tru) = 3 := by
  simp

/-! ## §6 The top scatter's rate constant

`SolveF7Bridge`'s `hKc` asks for `Kc ≤ ckc·(|x| + 1)` with `ckc` a
schedule constant, and this section supplies both halves of it for the
machine's own top-scatter stage:

* `f7_topScatK_le` — `topScatK N ns atoms ≤ f7ScatRate atoms ·
  (N + ns + 1)`, where `f7ScatRate` reads only the atoms' radii and
  witness counts. Every carrier figure in `topAtomK`, `scatterK` and
  `markK` is linear, and the landed `markK_le` supplies the only
  non-obvious step;
* `f7_carrier_slots_le` — on an encoding, `N + ns + 1 ≤ |x| + 1` once
  `N = n` and `ns ≤ 2·edgeCount x`, straight from `EncodesGraph`'s
  `length_eq` (`|x| = 3 + n + 2·edgeCount x`).

So the top scatter's cost **is** linear in the input at a schedule-only
rate — the question the bridge's binder order raises, answered in the
affirmative. What is not proved here is `∑ v, G.degree v = 2·edgeCount x`
(the identification of the stage's slot count `ns` with the encoding's
edge zone); that seam belongs to `TopScatterAll`'s own column, and
`f7_topScatK_le_word` takes it as the inequality `hns`. -/

/-- **The rate of one scatter atom's top-stage budget**: a figure of the
atom's radius and witness count, and of nothing else. -/
def f7AtomRate (r t : ℕ) : ℕ := 102 + 69 * (r + 1) * t + 30 * t

/-- **The rate of the whole stage**: one `f7AtomRate` per atom, plus the
closing skip. A function of the schedule's atom list alone — no carrier,
no graph, no word. -/
def f7ScatRate {Λc : ℕ} : List (ScatterSentence Λc) → ℕ
  | [] => 1
  | σa :: rest => f7AtomRate σa.r σa.t + f7ScatRate rest

/-- One atom's budget, at its rate. Every carrier figure in `topAtomK`
(the glue, the column loop, `scatterK`'s `41·N`, and `markK` through the
landed `markK_le`) is linear in `N + ns + 1`. -/
theorem f7_topAtomK_le (N ns r t : ℕ) :
    topAtomK N ns r t ≤ f7AtomRate r t * (N + ns + 1) := by
  have hm : markK N ns r ≤ 69 * (r + 1) * (N + ns + 1) := markK_le N ns r
  have e : topAtomK N ns r t = 45 + 57 * N + (markK N ns r + 30) * t := by
    simp only [topAtomK, scatterK]; ring
  have hA : (markK N ns r + 30) * t ≤ (69 * (r + 1) * (N + ns + 1) + 30) * t :=
    Nat.mul_le_mul_right _ (by omega)
  have hB : (69 * (r + 1) * (N + ns + 1) + 30) * t
      = 69 * (r + 1) * t * (N + ns + 1) + 30 * t := by ring
  have hC : 30 * t ≤ 30 * t * (N + ns + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hD : (45 : ℕ) ≤ 45 * (N + ns + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hE : 57 * N ≤ 57 * (N + ns + 1) := by omega
  have hF : f7AtomRate r t * (N + ns + 1)
      = 45 * (N + ns + 1) + 57 * (N + ns + 1) + 69 * (r + 1) * t * (N + ns + 1)
        + 30 * t * (N + ns + 1) := by simp only [f7AtomRate]; ring
  omega

/-- **The stage's budget, at its rate** — linear in the carrier plus the
slot count, with a constant that reads only the atoms. -/
theorem f7_topScatK_le {Λc : ℕ} (N ns : ℕ) :
    ∀ atoms : List (ScatterSentence Λc),
      topScatK N ns atoms ≤ f7ScatRate atoms * (N + ns + 1) := by
  intro atoms
  induction atoms with
  | nil =>
    simp only [topScatK, f7ScatRate]
    exact Nat.le_mul_of_pos_right _ (by omega)
  | cons σa rest ih =>
    rw [topScatK, f7ScatRate, Nat.add_mul]
    exact Nat.add_le_add (f7_topAtomK_le N ns σa.r σa.t) ih

/-- On an encoding, the carrier and the target zone together are the
word: `|x| = 3 + n + 2·edgeCount x`, so `n + ns + 1 ≤ |x| + 1` at every
slot count the target zone can supply. -/
theorem f7_carrier_slots_le {x : List ℕ} {n ns : ℕ} {G : SimpleGraph (Fin n)}
    (h : EncodesGraph x n G) (hns : ns ≤ 2 * edgeCount x) :
    n + ns + 1 ≤ x.length + 1 := by
  have := h.length_eq
  omega

/-- **`hKc`, supplied**: the top scatter's budget on an encoding is at
most the schedule rate times `|x| + 1`. This is the clause
`SolveF7CloseCompose.f7_bridge_bucket` asks of `TopScatterAll`, and the
answer to whether the constant can be schedule-only: it can. -/
theorem f7_topScatK_le_word {Λc : ℕ} (atoms : List (ScatterSentence Λc))
    {x : List ℕ} {n ns : ℕ} {G : SimpleGraph (Fin n)} (h : EncodesGraph x n G)
    (hns : ns ≤ 2 * edgeCount x) :
    topScatK n ns atoms ≤ f7ScatRate atoms * (x.length + 1) :=
  le_trans (f7_topScatK_le n ns atoms)
    (Nat.mul_le_mul_left _ (f7_carrier_slots_le h hns))

/-! ## §5 The leaf's axiom profile -/

#print axioms exprTemps_bcExpr_le

#print axioms f7Temps_le

#print axioms bcExpr_namesOk

#print axioms verdictCom_ok

#print axioms verdictCom_ok_f7Temps

#print axioms topCom_ok

#print axioms mcSolveCom_ok_f7Temps

#print axioms f7_bcExpr_ok_at_three

#print axioms f7_exprTemps_witness

#print axioms f7_topAtomK_le

#print axioms f7_topScatK_le

#print axioms f7_topScatK_le_word

end Lax3Proofs.Prog
