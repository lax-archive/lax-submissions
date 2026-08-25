import Lax3Proofs.ProgCodegenLayout
import Lax13Proofs.Refine.Codegen.Cash
import Lax3Proofs.Headline

/-!
# F6 — the machine realization, skeleton: one `ComputesInTime` for the
compiled whole, conditional on one named `Spec` obligation

The endorsed axiom
(`Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`)
needs a compiled `Lax13.Ram.Program` with

    ComputesInTime w p {x | EncodesGraph x n G ∧ side condition}
      (fun _ => if Sat G Fin.elim0 φ then [1] else [0]) T.

The tower's exit is `computesInTime_of_spec`
(`word-ram/proofs/Lax13Proofs/Refine/Codegen/Cash.lean:408-419`): a
`Com.Ok` layout check, an entry bound (`hinp`), one `Reasoning.Spec`
from `initEnv` to the output tape, and `FitsWords` (`hfit`). This file
assembles the pipeline at that exit **once**, so that everything still
missing from the campaign is a `Reasoning.Spec` obligation about an
IMP+ command — a finite proof obligation, not an open-ended
translation.

## The pipeline

`mcCom solveCom := parseCom ; solveCom ; writeScalar "verdict"` —

* **stage 1, the front end — discharged** (`ProgCodegenParse`):
  `parseCom` reads the CSR word into the frame (`CsrIn` descriptor),
  at cost `12·|x|` (F2's `chargeParse` at the harness constant);
* **stage 2, the solve stages — the named obligation** (`SolveSpec`):
  from `CsrIn`, leave in `"verdict"` the number
  `if unrolledMC (headlineSetup C hC φ) ord G (trivialColoring n)
  then 1 else 0` — the value F4's `mcProg` computes
  (`ProgDriver.mcProg_le_spec`: the returned proposition *is*
  `unrolledMC`), at a budget `Ks x` of the discharger's choosing;
* **stage 3, the epilogue — discharged**: `writeScalar`, cost `2`.

`mc_computesInTime_of_solveSpec` then lands the axiom's exact
`ComputesInTime` shape on the axiom's exact admissible set `mcD`
(verbatim), at time `mcLayout.const · (12·|x| + Ks x + 2)` — a constant
that does not see the layout's `temps` (`mcLayout_const_eq`). The `Sat`
form of the value function is produced here from the obligation's
`unrolledMC` form through the landed semantic chain
(`Unroll.unrolledMC_eq_MC` + `Headline.headlineSetup_mc_correct`) —
the machine side never mentions `Sat` again. The word-size side
condition is spent by `ProgCodegenLayout` (`hinp`/`hfit`), E13 item
(d).

## Judgment calls

**F6/D-a — one obligation, not a fake-precise list.** The solve stages
could be stubbed finer (per driver block, per routine), but every
finer cut fixes a machine *encoding* of an interface object — the
depth-`j` table as a bit matrix, the cover output as CSR rows — and
those encodings are exactly what the Sepref descent designs. Freezing
them here, before any synthesis, risks a skeleton whose seams no
synthesized command can meet. So the skeleton's Lean-level seam is the
one whose encoding is already fixed by landed material: the parsed
word (`CsrIn`, fixed by F2 + the harness) and the verdict cell. The
decomposition *plan* for `SolveSpec` is recorded below as the
continuation map.

**Binder order (the campaign's most-repeated gate).** The axiom's
`∃ p` precedes `∀ n G w`: one program for the whole class. This
theorem is stated at a fixed `(n, G, w)` because `ComputesInTime` is,
but every piece of program data — `solveCom`, `eS`, `eA`, `t`, `ord`,
`c`, `q`, `Ks` — is a parameter the caller fixes *before* `n`, `G`, `w`,
and the compiled program and the time bound mention none of them. F7
therefore instantiates all of them once from `(C, hC, φ, ε)` (the
`SolveSpec` discharge must be uniform in `(n, G, w)` — item 2 of the
continuation map produces one command for the class, its depth `ℓ+1`
a constant of the schedule) and applies this theorem pointwise under
the axiom's quantifiers; the `∃ p, ∃ T` closes over the uniform data.

**F6/D-b — the obligation's value is `unrolledMC`, not `Sat`.** The
discharger proves what the machine computes; `mcProg_le_spec` ends at
`unrolledMC`, and the semantic conversion to `Sat` is one landed
rewrite consumed here, once. Stating the obligation at `Sat` would
force every stage of the descent to carry the semantic chain.

**F6/D-c — two constants `q ≤ c`.** The value bound's constant `q` is
the schedule's (what the stages store: `≤ (2+c_S)·n²`, `Unroll` §11);
the axiom's `c` is chosen after it and absorbs the layout span
(`hspan`). This is §11's "choose `c` large enough" as two explicit
hypotheses, dischargeable by F7 with `omega` once `q` and the name
lists are concrete.

**F6/D-d — `ext` is a parameter with two pinned values.** The harness
pre-sizes arrays per input; the parse needs `"off"`/`"tgt"` at their
zone lengths, and the solve stages will size their own arrays (table,
cover rows, BFS scratch) — unknown here, so `ext` passes through and
`SolveSpec` is stated against the same `ext`.

## The continuation map (the campaign's remaining machine work)

Everything below discharges `SolveSpec C hC φ ord G c w q ext solveCom
Ks` — exhibit `solveCom`, `Ks`, `eS`, `eA`, `ext`, `q` and prove the
one `Spec`. In dependency order:

1. **Arena materialization + rows** (small): from `CsrIn`, the root
   frame's state. The graph-level bridge is landed:
   `Impl.blockMem`/`Impl.parseGraphAt_eq` pin `G.Adj` to the arrays
   (`csrOffsets`/`csrTargets` are `x.getD` at the zone positions —
   `csr_decomp`); `Impl.parse_rootArena` lands on
   `Driver.rootArena G col`. The color rows at `L = 0` are empty
   (`pal 0` may still be `> 0` — the rows are `recordProfiles`'
   output per frame, seam recorded in `ProgDriver`'s docstring).
2. **The `ℓ+1` driver blocks** (the bulk): `ProgDriver.driverProg`'s
   recursion is on the level index only, so the machine layout is
   `S.depth + 1` static code blocks, block `j` jumping into `j+1`
   (`Unroll`'s layout paragraph; `eS`/`eA` grow by a per-level family
   of names). Per block, the per-frame sequencing restrict → profiles
   → isolate → cover → recurse-readback → scatter, against the landed
   `Impl*` specs and `ProgFrame.frameProg_le_spec`'s shape. The
   descent route is `Refine/Sepref/` (`Translate`/`Monadify` to the
   IR) then `Refine/Codegen/Embed`+`Cash` (`spec_of_hnRefine`), as
   `EndToEnd.lean` §4 does per program; or direct `Spec`-kit loops
   as `ProgCodegenParse` does — per routine, whichever is shorter.
   **Hazard, recorded**: `botProg`'s fuel-0 *edged* branch is dead on
   the class (`Unroll.memLeaf_eq_bot` / `mkSetup_memLeaf_eq_bot`) and
   holds an abstract value no machine computes. The compiled block 0
   must implement only the edgeless route (`Impl.botEval` over rows,
   `ImplBot`), with the run invariant discharging the guard: state
   block 0's `Spec` under the invariant's edgeless hypothesis (the
   route `EndToEnd` takes for unreachable branches), or compile an
   explicit edge-count-zero guard whose edged branch has a
   `False`-premised `Spec`.
3. **The root evaluation** (small): `top`'s boolean combination with
   local-sentence atoms as compile-time constants (L1 `localConst`)
   and one guarded `Impl.greedyScatter` count per scatter atom
   (`ProgDriver.mcProg`'s shape, budget `topScatterCost`), reading
   the root table left by block 0's frame, writing `"verdict"`.
4. **The budget `Ks`**: alignment with the NREST charge total
   (`mcCharge`'s cash — the concurrent F6-charge leaf owns the
   `ACost`-side arithmetic; this file deliberately does not depend on
   it). F7 reconciles `Ks` against `headline_encoded`'s
   `dcost ≤ c·(|x|+1)^(1+ε)` chain and splits the ε-budget once —
   Headline Part 3(e).
5. **Values stored**: every stage must keep its stored values below
   `mcB q x = q·(|x|+1)²` — the §11 quantities (cover output sizes,
   table indices `≤ n·|ℱ_j|`, BFS counters) all fit at a schedule
   constant `q`; entries and lengths fit at `q = 1`
   (`entry_le_length`). Check per stage while discharging (2).

What F7 then does with this file's headline: instantiate, choose
`c ≥` the `hspan` sum, wrap `T x := mcLayout.const · (12·|x| + Ks x
+ 2)`, prove `(T x : ℝ) ≤ c'·(|x|+1)^(1+ε)` from (4), and `∃`-close
the axiom's statement.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen Lax13Proofs.Compile
open Lax13Proofs.Refine.Codegen (computesInTime_of_spec)
open Lax11.GraphEncoding
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)

/-! ## §1 The pipeline -/

/-- **The whole pipeline**: the front end, the solve stages (a
parameter until the descent delivers them), the verdict epilogue. -/
def mcCom (solveCom : Com) : Com :=
  .seq parseCom (.seq solveCom (writeScalar "verdict"))

/-- The front end compiles under the skeleton layout, whatever the
extension, as soon as the layout has the two temporaries the parse's
own array scans need. The landed proof is replayed at `t = 2` and
transported upward by `mcLayout_com_ok_mono` — `Com.Ok` is monotone in
`temps`, so nothing about the front end changes when F7 deepens the
layout for the root evaluation. -/
theorem parseCom_ok (eS eA : List String) {t : ℕ} (ht : 2 ≤ t) :
    Com.Ok (mcLayout eS eA t) parseCom :=
  mcLayout_com_ok_mono ht (by
    simp [parseCom, readScalars, readArr, Lax13Proofs.Reasoning.Lib.Fill.put,
      mcLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok])

/-- The pipeline compiles as soon as the solve stages do. The epilogue
`writeScalar "verdict"` needs one temporary (`Com.Ok (.write e)` asks
`0 < L.temps`), the front end two; both are under `2 ≤ t`. -/
theorem mcCom_ok {eS eA : List String} {t : ℕ} {solveCom : Com} (ht : 2 ≤ t)
    (h : Com.Ok (mcLayout eS eA t) solveCom) :
    Com.Ok (mcLayout eS eA t) (mcCom solveCom) :=
  ⟨parseCom_ok eS eA ht, h, by
    simp [writeScalar, mcLayout, Com.Ok, Expr.Ok]; omega⟩

/-! ## §2 The named obligation -/

open Classical in
/-- **The solve stages' obligation — the campaign's remaining machine
work, as one named `Spec`** (the continuation map in the module
docstring is its decomposition plan). From the parsed word (`CsrIn`),
on every admissible input, leave in `"verdict"` the number of the
proposition F4's `mcProg` computes — `unrolledMC` at the campaign
setup, which `mc_computesInTime_of_solveSpec` converts to the axiom's
`Sat` through the landed semantic chain. The budget `Ks` is the
discharger's; F7 reconciles it against the NREST charge total. -/
def SolveSpec (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ext : List ℕ → String → ℕ) (solveCom : Com)
    (Ks : List ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    Spec (mcB q x) (CsrIn (ext x) x) solveCom
      (fun _ σ' => σ'.vars "verdict" =
        if Unroll.unrolledMC (Headline.headlineSetup C hC φ) ord G
            (Impl.trivialColoring n) then 1 else 0)
      (Ks x)

/-- The pipeline's IMP+ budget: the front end's `12·|x|`, the solve
stages' `Ks x`, the epilogue's `2`. `computesInTime_of_spec`
multiplies exactly `mcLayout.const` on top — nothing else. -/
def mcK (Ks : List ℕ → ℕ) (x : List ℕ) : ℕ := 12 * x.length + Ks x + 2

/-! ## §3 The skeleton's headline -/

open Classical in
/-- **F6's conditional headline: the compiled pipeline decides `φ` on
the machine** — the endorsed axiom's `ComputesInTime`, on the axiom's
admissible set verbatim, conditional on the one named obligation
`SolveSpec` (plus its layout/bound bookkeeping). Everything else —
the front end, the epilogue, the semantic chain to `Sat`, the
word-size condition — is discharged here.

The remaining hypotheses are, in F7-discharge order: `hq`/`hqc`/`ht`/
`hspan` (constants: the schedule's `q`, the layout's temporaries `t`,
the axiom's `c` absorbing the span — `t` enters `hspan` additively and
`Layout.const` not at all), `hextOff`/`hextTgt` (the two pre-sized
parse arrays),
`hokS`/`hnw` (the solve command mentions only layout names and never
writes the tape), and `hsolve` (the obligation). -/
theorem mc_computesInTime_of_solveSpec
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (eS eA : List String) (t : ℕ) (ext : List ℕ → String → ℕ)
    (solveCom : Com) (Ks : List ℕ → ℕ)
    (hq : 1 ≤ q) (hqc : q ≤ c) (ht : 2 ≤ t)
    (hspan : 9 + t + eS.length + (2 + eA.length) * q ≤ c)
    (hextOff : ∀ x ∈ mcD n G c w, ext x "off" = vertexCount x + 1)
    (hextTgt : ∀ x ∈ mcD n G c w, ext x "tgt" = 2 * edgeCount x)
    (hokS : Com.Ok (mcLayout eS eA t) solveCom) (hnw : solveCom.NoWrite)
    (hsolve : SolveSpec C hC φ ord G c w q ext solveCom Ks) :
    Lax13.RamComputes.ComputesInTime w
      (compileProgram (mcLayout eS eA t) (mcCom solveCom))
      (mcD n G c w)
      (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0])
      (fun x => (mcLayout eS eA t).const * mcK Ks x) := by
  refine computesInTime_of_spec (mcCom_ok ht hokS) (mcD_entry_lt_mcB hq) ?_
    (mcLayout_fitsWords eS eA t hq hqc hspan)
  intro x hx
  obtain ⟨henc, hside⟩ := hx
  refine ⟨ext x, ?_⟩
  -- the semantic chain: the obligation's value is the axiom's value
  have hiff : Unroll.unrolledMC (Headline.headlineSetup C hC φ) ord G
      (Impl.trivialColoring n) ↔ Lax3.FirstOrder.Sat G Fin.elim0 φ := by
    rw [Unroll.unrolledMC_eq_MC]
    exact Headline.headlineSetup_mc_correct C hC φ ord G (Impl.trivialColoring n)
  have hone : 1 < mcB q x := one_lt_mcB (three_le_length henc) hq
  have hv01 : (if Lax3.FirstOrder.Sat G Fin.elim0 φ then (1 : ℕ) else 0)
      < mcB q x := by
    split <;> omega
  -- stage 1: the front end
  have hpar := parseCom_spec (mcB q x) (ext x) henc
    (length_add_one_lt_mcB (three_le_length henc) hq)
    (hextOff x ⟨henc, hside⟩) (hextTgt x ⟨henc, hside⟩)
  -- stage 2: the obligation, its value converted, its output tape framed
  have hsol : Spec (mcB q x) (CsrIn (ext x) x) solveCom
      (fun σ σ' => σ'.vars "verdict" =
          (if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0) ∧
        σ'.out = σ.out) (Ks x) := by
    refine ((hsolve x ⟨henc, hside⟩).frame).post ?_
    rintro σ σ' - ⟨hq', -, -, -, hout⟩
    refine ⟨?_, hout hnw⟩
    rw [hq']
    exact if_congr hiff rfl rfl
  -- stage 3: the epilogue
  have hwr := writeScalar_spec (mcB q x) "verdict"
    (if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0) hv01
  -- the chain
  have htail : Spec (mcB q x) (CsrIn (ext x) x)
      (.seq solveCom (writeScalar "verdict"))
      (fun σ σ'' => σ''.out = σ.out ++
        [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0]) (Ks x + 2) := by
    refine Spec.seq hsol hwr (fun _ _ _ hq' => hq'.1) ?_
    rintro σ σ' σ'' - ⟨-, hout⟩ rfl
    show σ'.out ++ _ = σ.out ++ _
    rw [hout]
  refine (Spec.seq hpar htail (fun _ _ _ hq' => hq') ?_).mono
    (by rw [mcK]; omega)
  rintro σ σ' σ'' - hcsr hout
  rw [hout, hcsr.out]
  simp only [List.nil_append]
  exact apply_ite (fun v : ℕ => ([v] : List ℕ))
    (Lax3.FirstOrder.Sat G Fin.elim0 φ) 1 0

end Lax3Proofs.Prog
