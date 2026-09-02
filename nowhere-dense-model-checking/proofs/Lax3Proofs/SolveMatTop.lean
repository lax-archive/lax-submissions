import Lax3Proofs.ProgCodegenLayout
import Lax3Proofs.ProgDriver

/-!
# F6b (part 2) — the root evaluation: `top`'s combination into `"verdict"`

`ProgDriver.mcProg`'s top shape (§5 lines 1–6): evaluate `top S` with
its local sentence atoms as compile-time constants (L1, `localConst`)
and its scatter atoms decided by the guarded greedy scatter counts over
the root table. This file is that evaluation as IMP+, parameterized the
way F6 parameterized `SolveSpec`:

* **the table and its state are parameters.** The root-eval `Spec`'s
  precondition is an abstract predicate `Q` — "the state holds the
  depth-0 table per the block family's own descriptor" — and the
  per-atom counts enter as an *expression valuation* `av` with one
  evaluation hypothesis (`hav`): under `Q`, the expression `av σa`
  reads the guard bit `scatterBit G T σa` of atom `σa` off the state.
  Freezing a concrete cell layout for the table or the counts here
  would commit the block family's encodings before their synthesis
  (F6/D-a); the driver-block leaf (F6c) instantiates `Q` with its
  exported table descriptor and `av` with its count cells.
* **the boolean combination is compile-time structure** (`bcExpr`):
  `top S` is a `BC` over `DistFO L 0 ⊕ ScatterSentence L`, and the
  code generator folds it into **one expression** — `localConst`
  atoms become literal bits (they are sentences: their truth is fixed
  before the input exists), scatter atoms become `av`'s reads,
  negation is `1 − ·`, conjunction is `·  * ·` on `{0,1}` values.
  `bcExpr_evalB` prices and evaluates it in one induction: the value
  is the bit of `(top S).eval` at the corresponding valuation, and
  every intermediate value is `0` or `1` — no bound above `1 < B` is
  ever needed.
* **the verdict is one assignment** (`verdictCom`), cost
  `topEvalCost S av = 1 + size(bcExpr)` — a constant of the schedule
  and of the block family's read expressions, independent of the
  input. `verdictCom_spec` is the general form at an arbitrary table
  `T`; `verdictCom_spec_mc` instantiates `T` at the root table
  `Unroll.unrolledTables … (rootArena G col)` and crosses
  `le_greedyScatter_iff` (at the canonical choice) to land on the
  exact `SolveSpec` value `if Unroll.unrolledMC S ord G col then 1
  else 0`. `topCom`/`topCom_spec` sequence the block family's scatter
  stage in front — the composed command has `SolveSpec`'s
  postcondition shape verbatim.

**Layout note (for F7's `Com.Ok` discharge).** `bcExpr` is one nested
expression, and `Expr.Ok` demands `depth < L.temps` at every node
with a subexpression (the compiler works in the `temps + 2` cells the
layout reserves); `mcLayout`'s base `temps = 2` will not compile a
deep combination. This is the extension `ProgCodegenLayout`'s docstring
already provides for ("a bigger `temps` only shifts the constant in
`hspan`"): F7 instantiates the layout with `temps ≥` the compiled
combination's depth — a constant of the schedule, fixed with `eS`/`eA`
before the input.

## The named slot obligation

What remains machine-side of the root evaluation is exactly the `hav`
hypothesis at the block family's `Q`: per scatter atom, the guarded
greedy count over the root table — `ImplScatter.greedyScatter`'s sweep
with one ball-marking BFS per non-final pick. Its budget is the landed
`ProgDriver.topScatterCost` / `ProgCharge.topBudget` column; the
**`t = 0` guard is a cost clause** and must stay visible in the
discharging program's text (`greedyScatterCost_zero` prices it —
`scatterBit` keeps the guard through `greedyScatter`'s own leading
`if t = 0`).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun
open Lax3Proofs.BCAlgebra

variable {L : ℕ}

/-! ## §1 The combination, compiled to one expression -/

open Classical in
/-- **The code generator for a locality combination**: `localConst`
atoms are compile-time bits (L1 — they are sentences), scatter atoms
are the caller's read expressions, negation is `1 − ·`, conjunction is
multiplication on `{0,1}`. -/
noncomputable def bcExpr (av : ScatterSentence L → Expr) :
    BC (DistFO L 0 ⊕ ScatterSentence L) → Expr
  | .atom (.inl ψ) => .lit (if localConst ψ then 1 else 0)
  | .atom (.inr σa) => av σa
  | .tru => .lit 1
  | .not b => .sub (.lit 1) (bcExpr av b)
  | .and b c => .mul (bcExpr av b) (bcExpr av c)

open Classical in
/-- **The compiled combination evaluates to the truth bit**, by one
induction: given that every scatter read delivers its atom's bit, the
whole expression delivers `(top)`'s bit — and every intermediate value
is `0` or `1`, so `1 < B` is the only bound ever consumed. The
valuation `v` is abstract; the two atom hypotheses tie it to
`localConst` on the left and to the reads on the right. -/
theorem bcExpr_evalB {B : ℕ} (h1B : 1 < B) {σ : Env}
    {v : DistFO L 0 ⊕ ScatterSentence L → Prop}
    {av : ScatterSentence L → Expr}
    (b : BC (DistFO L 0 ⊕ ScatterSentence L))
    (hloc : ∀ ψ, Sum.inl ψ ∈ b.atoms → (v (Sum.inl ψ) ↔ localConst ψ))
    (hav : ∀ σa, Sum.inr σa ∈ b.atoms →
      (av σa).evalB B σ = some (if v (Sum.inr σa) then 1 else 0)) :
    (bcExpr av b).evalB B σ = some (if b.eval v then 1 else 0) := by
  induction b with
  | atom a =>
    rcases a with ψ | σa
    · simp only [bcExpr]
      rw [evalB_lit (by split <;> omega)]
      have hiff : BC.eval v (.atom (.inl ψ)) ↔ localConst ψ :=
        hloc ψ (by rw [atoms_atom]; exact List.mem_singleton_self _)
      exact congrArg some (if_congr hiff rfl rfl).symm
    · simp only [bcExpr]
      rw [hav σa (by rw [atoms_atom]; exact List.mem_singleton_self _)]
      -- `BC.eval v (.atom (.inr σa))` is `v (Sum.inr σa)` definitionally
      rfl
  | tru =>
    simp only [bcExpr]
    rw [evalB_lit h1B]
    exact congrArg some (if_pos trivial).symm
  | not b ih =>
    simp only [bcExpr]
    have hb := ih (fun ψ h => hloc ψ h) (fun σa h => hav σa h)
    have hev := evalB_bin (op := .sub) (e := Expr.lit 1) (f := bcExpr av b)
      (evalB_lit h1B) hb (by simp only [Bop.apply_sub]; split <;> omega)
    rw [Expr.sub_def, hev]
    simp only [Bop.apply_sub]
    by_cases h : BC.eval v b
    · rw [if_pos h, if_neg (fun hn => ((eval_not b).mp hn) h)]
    · rw [if_neg h, if_pos ((eval_not b).mpr h)]
  | and b c ihb ihc =>
    simp only [bcExpr]
    have hb := ihb
      (fun ψ h => hloc ψ (by rw [atoms_and]; exact List.mem_append_left _ h))
      (fun σa h => hav σa (by rw [atoms_and]; exact List.mem_append_left _ h))
    have hc := ihc
      (fun ψ h => hloc ψ (by rw [atoms_and]; exact List.mem_append_right _ h))
      (fun σa h => hav σa (by rw [atoms_and]; exact List.mem_append_right _ h))
    have hev := evalB_bin (op := .mul) (e := bcExpr av b) (f := bcExpr av c)
      hb hc (by simp only [Bop.apply_mul]; split <;> split <;> omega)
    rw [Expr.mul_def, hev]
    simp only [Bop.apply_mul]
    by_cases hbv : BC.eval v b <;> by_cases hcv : BC.eval v c <;>
      simp [eval_and b c, hbv, hcv]

/-! ## §2 The verdict assignment -/

open Classical in
/-- **The scatter slot's per-atom target**: the guard bit of atom `σa`
over table `T` — `1` iff the guarded greedy count reaches the demanded
`t`. The `t = 0` guard rides inside `greedyScatter`'s own text; its
cost side is the landed `greedyScatterCost_zero`. -/
noncomputable def scatterBit {n : ℕ} (G : SimpleGraph (Fin n))
    (T : Fin n → DistFO L 1 → Prop) (σa : ScatterSentence L) : ℕ :=
  if σa.t ≤ Impl.greedyScatter G σa.r {v : Fin n | T v σa.β} σa.t then 1 else 0

/-- **The root evaluation's tail**: `top`'s combination, folded into
the verdict cell as one assignment. -/
noncomputable def verdictCom (S : Setup L) (av : ScatterSentence L → Expr) : Com :=
  .assign "verdict" (bcExpr av (top S))

/-- The tail's price: one assignment of the compiled combination — a
constant of the schedule and of the slot's read expressions,
independent of the input. -/
noncomputable def topEvalCost (S : Setup L) (av : ScatterSentence L → Expr) : ℕ :=
  1 + (bcExpr av (top S)).size

open Classical in
/-- **The verdict, at an arbitrary table `T`**: from any state
description `Q` under which the reads deliver the guard bits over `T`
(`hav` — the named slot obligation), the tail leaves in `"verdict"`
the bit of `top`'s evaluation with the scatter atoms decided by the
guarded counts. -/
theorem verdictCom_spec (B : ℕ) (S : Setup L) {n : ℕ}
    (G : SimpleGraph (Fin n)) (T : Fin n → DistFO L 1 → Prop)
    (av : ScatterSentence L → Expr) (Q : Env → Prop) (h1B : 1 < B)
    (hav : ∀ σ, Q σ → ∀ σa ∈ scatterAtoms S.choice S.φ S.hφ,
      (av σa).evalB B σ = some (scatterBit G T σa)) :
    Spec B Q (verdictCom S av)
      (fun σ σ' => σ' = σ.setVar "verdict"
        (if (top S).eval (Sum.elim (fun ψ => localConst ψ)
          (fun σa => σa.t ≤ Impl.greedyScatter G σa.r
            {v : Fin n | T v σa.β} σa.t)) then 1 else 0))
      (topEvalCost S av) := by
  refine Spec.assign (f := fun _ => if (top S).eval _ then 1 else 0) ?_
  intro σ hσ
  refine bcExpr_evalB h1B (top S) (fun ψ _ => Iff.rfl)
    (fun σa hmem => (hav σ hσ σa (mem_scatterAtoms.mpr hmem)).trans
      (congrArg some ?_))
  -- the slot's bit is the valuation's bit (`Nat.decLe` on the left,
  -- the classical instance on the right — `if_congr` crosses them)
  rw [scatterBit]
  exact if_congr Iff.rfl rfl rfl

open Classical in
/-- **The verdict, at the root table** — the `SolveSpec` value: with
the canonical scatter choice and the reads delivering the guard bits
over the root table `Unroll.unrolledTables … (rootArena G col)` (the
table the driver blocks leave behind — `driverProg_le_spec_root`'s
value through `unrolledTables_eq_tables`), the tail leaves in
`"verdict"` exactly `if Unroll.unrolledMC S ord G col then 1 else 0`,
through `le_greedyScatter_iff` — the guarded count decides each
scatter atom exactly. -/
theorem verdictCom_spec_mc (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L)
    (av : ScatterSentence L → Expr) (Q : Env → Prop)
    (hchoice : S.choice = greedyChoice) (h1B : 1 < B)
    (hav : ∀ σ, Q σ → ∀ σa ∈ scatterAtoms S.choice S.φ S.hφ,
      (av σa).evalB B σ = some (scatterBit G
        (Unroll.unrolledTables S ord 0 (rootArena G col)) σa)) :
    Spec B Q (verdictCom S av)
      (fun σ σ' => σ' = σ.setVar "verdict"
        (if Unroll.unrolledMC S ord G col then 1 else 0))
      (topEvalCost S av) := by
  refine (verdictCom_spec B S G (Unroll.unrolledTables S ord 0 (rootArena G col))
    av Q h1B hav).post ?_
  rintro σ σ' - hσ'
  rw [hσ']
  congr 1
  refine if_congr ?_ rfl rfl
  rw [Unroll.unrolledMC]
  refine eval_congr (top S) fun a _ => ?_
  cases a with
  | inl ψ => exact Iff.rfl
  | inr σa =>
    simp only [Sum.elim_inr, hchoice]
    exact Impl.le_greedyScatter_iff _ _ _ _

/-! ## §3 The composed root evaluation -/

/-- **The root evaluation** (§5 lines 1–6, as IMP+): the block
family's scatter stage — the guarded sweeps computing the per-atom
counts, a parameter with a spec-and-charge pair exactly as `frameProg`
takes its slots — then the compiled combination into `"verdict"`. -/
noncomputable def topCom (scatCom : Com) (S : Setup L)
    (av : ScatterSentence L → Expr) : Com :=
  .seq scatCom (verdictCom S av)

open Classical in
/-- **The composed root evaluation's `Spec`** — the exact postcondition
shape `SolveSpec` asks of the pipeline's tail: given the scatter
stage's own spec (`hscat`: from the block family's table state `P`,
establish the read state `Q` for budget `Kc` — `topScatterCost` is the
advertised column) and the read obligation `hav`, the composed command
leaves `"verdict" = if unrolledMC then 1 else 0`, for `Kc` plus the
constant tail. -/
theorem topCom_spec (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {n : ℕ} (G : SimpleGraph (Fin n)) (col : Coloring n L)
    (av : ScatterSentence L → Expr) {P Q : Env → Prop} {scatCom : Com} {Kc : ℕ}
    (hchoice : S.choice = greedyChoice) (h1B : 1 < B)
    (hscat : Spec B P scatCom (fun _ σ' => Q σ') Kc)
    (hav : ∀ σ, Q σ → ∀ σa ∈ scatterAtoms S.choice S.φ S.hφ,
      (av σa).evalB B σ = some (scatterBit G
        (Unroll.unrolledTables S ord 0 (rootArena G col)) σa)) :
    Spec B P (topCom scatCom S av)
      (fun _ σ' => σ'.vars "verdict" =
        if Unroll.unrolledMC S ord G col then 1 else 0)
      (Kc + topEvalCost S av) := by
  refine Spec.seq hscat
    (verdictCom_spec_mc B S ord G col av Q hchoice h1B hav)
    (fun _ σ' _ hq => hq) ?_
  rintro σ σ' σ'' - - rfl
  simp

end Lax3Proofs.Prog
