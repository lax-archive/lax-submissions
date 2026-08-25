import Lax3Proofs.ProgCodegen
import Lax3Proofs.ProgCoverChargeDeg
import Lax3Proofs.SolveChain
import Lax3.ModelChecking

/-!
# F7-c — the last mile: from `SolveSpec` to the endorsed axiom

`ProgCodegen.mc_computesInTime_of_solveSpec` lands the endorsed axiom's
`ComputesInTime`, on the axiom's admissible set verbatim, at the machine
budget `(mcLayout eS eA).const · mcK Ks x`, conditional on eight named
hypotheses. This file spends the last three of them —
`hq`/`hqc`/`hspan`, the constants — closes the `∃ p c T` and proves the
axiom's *real* time bound, taking only `SolveSpec` and the ledger
bridge as hypotheses.

## What the close actually needs, and in which direction

Three monotonicities carry the whole file, and each one runs the way
the axiom's shape needs:

* **the admissible set is antitone in `c`** (`mcD_mono_c`): a larger
  constant makes `c·(|x|+v+1)² ≤ 2^w` harder, so `mcD n G c w ⊆
  mcD n G c₀ w`. So the `SolveSpec` discharger may fix its own `c₀`,
  and F7 is free to raise `c` afterwards for the span and the time
  bound. `solveSpec_mono_c` transports the obligation itself.
* **`ComputesInTime` is monotone in `T`** (`computesInTime_mono`):
  `∃ t ≤ T₀ x` gives `∃ t ≤ T x` whenever `T₀ x ≤ T x` *on the
  admissible set*. So the machine's own budget must sit **under** the
  advertised `T` — while `T`'s real-valued bound sits **above** it.
  The two inequalities point in opposite directions and `f7T` is
  chosen to be exactly the composite of the two bridges, so neither is
  slack.
* **the axiom's `c` occurs twice, and both occurrences are helped by
  raising it**: in the admissible set (shrinking it) and in
  `T x ≤ c·(|x|+1)^{1+ε}` (weakening it). This is why one constant can
  serve both, and it is the reason the close is a `max`/sum and not a
  fixed point.

## `q` is not free — and `c` is

`q` sizes the *value* bound `mcB q x = q·(|x|+1)²`, which appears
inside `SolveSpec`'s `Spec`, so it cannot be raised after the fact:
`Spec B` is not monotone in `B`. Every lower bound on `q` therefore has
to be collected before the discharge. They are collected in
`SolveF7CloseQ`, where `f7q` takes the max; this file only asks
`1 ≤ q`.

`c`, by contrast, is chosen here, after everything:

    f7c := c₀ + q + (11 + |eS| + (2 + |eA|)·q) + ⌈f7cR⌉₊

— the discharger's own constant, the `hqc` bound, the `hspan` span, and
the ceiling of the real constant the time bound needs. Adding rather
than maxing keeps every side condition an `omega` step.

## The time bound

`exists_mcChargeMS_T_bucket_coverColumn` (landed, `ProgCoverChargeDeg`)
gives, at one `cf ≥ 1`, a **single** `T_ch : List ℕ → ℕ` with
`(T_ch x : ℝ) ≤ c'·(|x|+1)^{1+ε}` and
`chargeTotal (mcChargeMS …) ≤ T_ch x` on every member of the class and
every encoding of it — uniformly in `n`, `G`, the coloring and
`htabF`. The bridge turns that into a bound on `Ks`, and

    f7T x := (mcLayout eS eA).const · (12·|x| + cB·(T_ch x + |x| + 1) + 2)

is then a function of `x` alone, above the machine's budget on every
admissible input and below `c·(|x|+1)^{1+ε}` on every input at all.

**Why the bridge has to be uniform.** `SolveChain.KsChargeBridge` puts
its constant `cB` *inside* the fixed `(n, G, c, w)`. The axiom's `T` is
fixed before `n` and `G`, so a `cB` that varies with the graph gives no
`T` at all — and it cannot be uniformized after the fact, because an
encoding `x` determines its own `(n, G)`, so the family
`{cB(n, G)}` is genuinely unbounded in general. `F7Bridge` below is
therefore the same statement with the existential pulled out in front
of `n`, `G`, `w` (and of the cover constant `cf`, which the landed
charge theorem produces rather than consumes);
`ksChargeBridge_of_f7Bridge` records that it implies the landed
obligation at every instance, so nothing is weakened — the strengthening
is on the hypothesis side. This is a **finding about
`KsChargeBridge`'s quantifier order**, recorded in the report.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax11.GraphEncoding
open Lax3.ColoredGraphs
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver Lax3Proofs.CoverRoutine
open Lax13Proofs.Refine (ACost)

/-! ## §1 The two monotonicities the close runs on -/

/-- **The admissible set is antitone in the axiom's constant.** Raising
`c` only makes the word-size side condition harder, so every input
admissible at the larger constant was admissible at the smaller one.
This is what lets the `SolveSpec` discharger fix its own `c₀` and F7
raise `c` afterwards. -/
theorem f7_mcD_mono_c {n : ℕ} {G : SimpleGraph (Fin n)} {c₀ c w : ℕ}
    (h : c₀ ≤ c) : mcD n G c w ⊆ mcD n G c₀ w := by
  rintro x ⟨henc, hside⟩
  refine ⟨henc, fun v hv => ?_⟩
  exact le_trans (Nat.mul_le_mul_right _ h) (hside v hv)

/-- `SolveSpec` transports upward along the constant: its only use of
`c` is the domain `mcD n G c w`, which shrinks. -/
theorem f7_solveSpec_mono_c (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    {c₀ c w q : ℕ} (ext : List ℕ → String → ℕ) (solveCom : Com)
    (Ks : List ℕ → ℕ) (h : c₀ ≤ c)
    (hs : SolveSpec C hC φ ord G c₀ w q ext solveCom Ks) :
    SolveSpec C hC φ ord G c w q ext solveCom Ks :=
  fun x hx => hs x (f7_mcD_mono_c h hx)

/-- **`ComputesInTime` is monotone in the time bound** — on the
admissible set only, which is all the axiom asks. -/
theorem f7_computesInTime_mono {w : ℕ} {p : Lax13.Ram.Program}
    {D : Set (List ℕ)} {f : List ℕ → List ℕ} {T₀ T : List ℕ → ℕ}
    (h : Lax13.RamComputes.ComputesInTime w p D f T₀)
    (hle : ∀ x ∈ D, T₀ x ≤ T x) :
    Lax13.RamComputes.ComputesInTime w p D f T := by
  intro x hx
  obtain ⟨t, ht, hrun⟩ := h x hx
  exact ⟨t, le_trans ht (hle x hx), hrun⟩

/-! ## §2 The ledger bridge, with the constant where the axiom needs it -/

open Classical in
/-- **The ledger bridge, uniform in the graph** — `SolveChain.KsChargeBridge`
with its constant `cB` pulled out in front of `n`, `G`, `w`, and with
the cover family's own constant `cf` universally quantified (the landed
charge theorem *produces* `cf`, so F7 cannot pin it before asking for
the bridge).

The `∀ cf` is not a strengthening in substance: `chargeTotal` of the
cover family is monotone in `cf` in every landed pricing, so a bridge
at `cf = 1` gives one at every `cf ≥ 1` at the same `cB`. The `∃ cB`
in front *is* the substantive difference, and it is forced by the
axiom's binder order. -/
def F7Bridge (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (ε : ℝ)
    (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (c₀ : ℕ) (Ks : List ℕ → ℕ) : Prop :=
  ∃ cB : ℕ, ∀ cf : ℝ, 1 ≤ cf →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w,
        Ks x ≤ cB * (chargeTotal
          (mcChargeMS (Headline.headlineSetup C hC φ)
            (selOrderingRoutine (fun m => bucketSel m)
              (3 * (Headline.headlineSetup C hC φ).R))
            ℓp (htabF n)
            (coverCFSel (fun m => bucketSel m) (Headline.headlineSetup C hC φ) cf
              (headlineδ (Headline.headlineSetup C hC φ) ε))
            G (Impl.trivialColoring n)) + x.length + 1)

open Classical in
/-- **The uniform bridge implies the landed obligation, at every
instance** — so `F7Bridge` is a strengthening of
`SolveChain.KsChargeBridge` and never a substitute for it. -/
theorem ksChargeBridge_of_f7Bridge (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ε : ℝ) (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (c₀ : ℕ) (Ks : List ℕ → ℕ) (h : F7Bridge C hC φ ε ℓp htabF c₀ Ks)
    (cf : ℝ) (hcf : 1 ≤ cf) (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ)
    (hG : C n G) :
    KsChargeBridge C hC φ
      (selOrderingRoutine (fun m => bucketSel m)
        (3 * (Headline.headlineSetup C hC φ).R))
      G c₀ w ℓp (htabF n)
      (coverCFSel (fun m => bucketSel m) (Headline.headlineSetup C hC φ) cf
        (headlineδ (Headline.headlineSetup C hC φ) ε))
      Ks := by
  obtain ⟨cB, hcB⟩ := h
  exact ⟨cB, hcB cf hcf n G w hG⟩

/-! ## §3 The real-valued arithmetic of the time bound -/

/-- `|x| + 1 ≤ (|x|+1)^{1+ε}` — the only fact about the exponent the
close uses, and the reason a linear overhead never inflates it. -/
theorem f7_le_rpow (x : List ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((x.length : ℝ) + 1) ≤ ((x.length : ℝ) + 1) ^ (1 + ε) := by
  have h1 : (1 : ℝ) ≤ (x.length : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (x.length : ℝ) := Nat.cast_nonneg _
    linarith
  calc ((x.length : ℝ) + 1) = ((x.length : ℝ) + 1) ^ (1 : ℝ) :=
        (Real.rpow_one _).symm
    _ ≤ ((x.length : ℝ) + 1) ^ (1 + ε) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

theorem f7_one_le_rpow (x : List ℕ) {ε : ℝ} (hε : 0 < ε) :
    (1 : ℝ) ≤ ((x.length : ℝ) + 1) ^ (1 + ε) := by
  have h1 : (1 : ℝ) ≤ (x.length : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (x.length : ℝ) := Nat.cast_nonneg _
    linarith
  exact le_trans h1 (f7_le_rpow x hε)

/-! ## §4 The close -/

open Classical in
/-- **F7-c's headline: the endorsed axiom's `∃ p c T`, from `SolveSpec`
and the uniform ledger bridge.**

Everything between `ProgCodegen`'s conditional headline and the axiom
is here: the constants (`hq`/`hqc`/`hspan` are spent — `f7c` is built
to satisfy the last two), the `∃`-closure, the identification of the
axiom's admissible set with `mcD`, and the real-valued time bound.
What stays open is exactly the two hypotheses the siblings own —
`hsolve` (the machine's `SolveSpec`, at the machine's own ordering
routine `selOrderingRoutine bucketSel (3·R)`) and `hbr` (the ledger
bridge, uniform).

The ordering routine is pinned, not free: the time bound is produced by
`exists_mcChargeMS_T_bucket_coverColumn`, which prices the charge ledger
at that routine, so `SolveSpec`'s `ord` and the bridge's must be that
one for the two halves to meet.

Nothing about the axiom is weakened: the exponent is `1 + ε`, the
admissible set is the axiom's set-builder verbatim, and the word-size
side condition is per-`(n, G, w)` inside, as the axiom states it. -/
theorem f7close_exists_of_solveSpec
    (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (ε : ℝ) (hε : 0 < ε)
    (q c₀ : ℕ) (eS eA : List String) (ext : List ℕ → String → ℕ)
    (solveCom : Com) (Ks : List ℕ → ℕ) (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hq : 1 ≤ q)
    (hokS : Com.Ok (mcLayout eS eA) solveCom) (hnw : solveCom.NoWrite)
    (hextOff : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w, ext x "off" = vertexCount x + 1)
    (hextTgt : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w, ext x "tgt" = 2 * edgeCount x)
    (hsolve : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      SolveSpec C hC φ
        (selOrderingRoutine (fun m => bucketSel m)
          (3 * (Headline.headlineSetup C hC φ).R))
        G c₀ w q ext solveCom Ks)
    (hbr : F7Bridge C hC φ ε ℓp htabF c₀ Ks) :
    ∃ (p : Lax13.Ram.Program) (c : ℕ) (T : List ℕ → ℕ),
      (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
        Lax13.RamComputes.ComputesInTime w p
          {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
          (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]) T := by
  classical
  -- the charge ledger's uniform time bound, at the machine's own routine
  obtain ⟨cf, c', Tch, hcf1, hc'0, hTch, hledger, -⟩ :=
    exists_mcChargeMS_T_bucket_coverColumn C hC φ hε ℓp
  obtain ⟨cB, hcB⟩ := hbr
  set K : ℕ := (mcLayout eS eA).const with hK
  -- the advertised time bound: a function of `x` alone
  set T : List ℕ → ℕ := fun x => K * (12 * x.length + cB * (Tch x + x.length + 1) + 2)
    with hT
  -- the real constant it needs, and the axiom's constant
  set cR : ℝ := (K : ℝ) * (14 + (cB : ℝ)) + (K : ℝ) * (cB : ℝ) * c' with hcR
  refine ⟨compileProgram (mcLayout eS eA) (mcCom solveCom),
    c₀ + q + (11 + eS.length + (2 + eA.length) * q) + ⌈cR⌉₊, T, ?_, ?_⟩
  · -- the real-valued bound: linear overhead never inflates the exponent
    intro x
    set P : ℝ := ((x.length : ℝ) + 1) ^ (1 + ε) with hP
    have hP1 : (1 : ℝ) ≤ P := f7_one_le_rpow x hε
    have hPlen : ((x.length : ℝ) + 1) ≤ P := f7_le_rpow x hε
    have hPlen' : ((x.length : ℝ)) ≤ P := le_trans (by linarith) hPlen
    have hTchP : ((Tch x : ℕ) : ℝ) ≤ c' * P := hTch x
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    have hcBnn : (0 : ℝ) ≤ (cB : ℝ) := Nat.cast_nonneg _
    have hstep : (T x : ℝ) ≤ cR * P := by
      have hcast : (T x : ℝ)
          = (K : ℝ) * (12 * (x.length : ℝ)
              + (cB : ℝ) * ((Tch x : ℝ) + (x.length : ℝ) + 1) + 2) := by
        rw [hT]; push_cast; ring
      rw [hcast, hcR]
      have h1 : (12 : ℝ) * (x.length : ℝ) ≤ 12 * P := by linarith
      have h2 : (cB : ℝ) * ((Tch x : ℝ) + (x.length : ℝ) + 1)
          ≤ (cB : ℝ) * (c' * P + P) := by
        refine mul_le_mul_of_nonneg_left ?_ hcBnn
        linarith
      have h3 : (2 : ℝ) ≤ 2 * P := by linarith
      nlinarith [hKnn, hcBnn, hP1]
    have hceil : cR ≤ (⌈cR⌉₊ : ℝ) := Nat.le_ceil _
    have hPnn : (0 : ℝ) ≤ P := le_trans zero_le_one hP1
    have hcle : ((⌈cR⌉₊ : ℕ) : ℝ)
        ≤ ((c₀ + q + (11 + eS.length + (2 + eA.length) * q) + ⌈cR⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left _ _
    calc (T x : ℝ) ≤ cR * P := hstep
      _ ≤ (⌈cR⌉₊ : ℝ) * P := mul_le_mul_of_nonneg_right hceil hPnn
      _ ≤ ((c₀ + q + (11 + eS.length + (2 + eA.length) * q) + ⌈cR⌉₊ : ℕ) : ℝ) * P :=
          mul_le_mul_of_nonneg_right hcle hPnn
  · -- the machine, per `(n, G, w)`
    intro n G w hG
    set c : ℕ := c₀ + q + (11 + eS.length + (2 + eA.length) * q) + ⌈cR⌉₊ with hc
    have hc₀c : c₀ ≤ c := by omega
    have hqc : q ≤ c := by omega
    have hspan : 11 + eS.length + (2 + eA.length) * q ≤ c := by omega
    have hmach := mc_computesInTime_of_solveSpec C hC φ
      (selOrderingRoutine (fun m => bucketSel m)
        (3 * (Headline.headlineSetup C hC φ).R))
      G c w q eS eA ext solveCom Ks hq hqc hspan
      (fun x hx => hextOff n G w hG x (f7_mcD_mono_c hc₀c hx))
      (fun x hx => hextTgt n G w hG x (f7_mcD_mono_c hc₀c hx))
      hokS hnw
      (f7_solveSpec_mono_c C hC φ _ G ext solveCom Ks hc₀c (hsolve n G w hG))
    refine f7_computesInTime_mono hmach ?_
    rintro x hx
    have hx₀ : x ∈ mcD n G c₀ w := f7_mcD_mono_c hc₀c hx
    have hKs : Ks x ≤ cB * (chargeTotal
        (mcChargeMS (Headline.headlineSetup C hC φ)
          (selOrderingRoutine (fun m => bucketSel m)
            (3 * (Headline.headlineSetup C hC φ).R))
          ℓp (htabF n)
          (coverCFSel (fun m => bucketSel m) (Headline.headlineSetup C hC φ) cf
            (headlineδ (Headline.headlineSetup C hC φ) ε))
          G (Impl.trivialColoring n)) + x.length + 1) :=
      hcB cf hcf1 n G w hG x hx₀
    have hch : chargeTotal
        (mcChargeMS (Headline.headlineSetup C hC φ)
          (selOrderingRoutine (fun m => bucketSel m)
            (3 * (Headline.headlineSetup C hC φ).R))
          ℓp (htabF n)
          (coverCFSel (fun m => bucketSel m) (Headline.headlineSetup C hC φ) cf
            (headlineδ (Headline.headlineSetup C hC φ) ε))
          G (Impl.trivialColoring n)) ≤ Tch x :=
      hledger n G hG (Impl.trivialColoring n) (htabF n) x hx.1
    have hKsT : Ks x ≤ cB * (Tch x + x.length + 1) :=
      le_trans hKs (Nat.mul_le_mul_left _ (by omega))
    have : mcK Ks x ≤ 12 * x.length + cB * (Tch x + x.length + 1) + 2 := by
      rw [mcK]; omega
    exact Nat.mul_le_mul_left K this

/-! ## §5 The axiom's statement, verbatim -/

open Classical in
/-- The endorsed axiom's statement, transcribed. The `example` below
checks the transcription is definitionally the axiom's own type; it is
the only place in this file that mentions the axiom, and it produces no
declaration. -/
def F7Goal : Prop :=
  ∀ (C : GraphClass), NowhereDense C →
  ∀ (φ : FO 0) (ε : ℝ), 0 < ε →
    ∃ (p : Lax13.Ram.Program) (c : ℕ) (T : List ℕ → ℕ),
      (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
        Lax13.RamComputes.ComputesInTime w p
          {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}
          (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0])
          T

-- Verbatim check: `F7Goal` is the endorsed axiom's type on the nose.
example : F7Goal := Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking

open Classical in
/-- **The whole F7 hypothesis, packaged** — every piece of program data
the axiom's binder order forces to be fixed before `n`, `G`, `w`, and
the four facts about it. This is exactly what the campaign's remaining
machine work has to produce, once, per `(C, φ, ε)`.

Anti-vacuity: this is an existential over *data*, so a discharger must
exhibit the command, the name lists, the array sizing and the budget —
it cannot be met by a vacuous predicate. The two propositional
components (`SolveSpec`, `F7Bridge`) are quantified over `x` in a set
that is inhabited exactly when the graph has an encoding admissible at
the word length, which is the axiom's own condition. -/
def F7Package (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (ε : ℝ) :
    Prop :=
  ∃ (q c₀ : ℕ) (eS eA : List String) (ext : List ℕ → String → ℕ)
    (solveCom : Com) (Ks : List ℕ → ℕ) (ℓp : ℕ → ℕ)
    (htabF : (n : ℕ) → (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N)),
    1 ≤ q ∧
    Com.Ok (mcLayout eS eA) solveCom ∧ solveCom.NoWrite ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w, ext x "off" = vertexCount x + 1) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      ∀ x ∈ mcD n G c₀ w, ext x "tgt" = 2 * edgeCount x) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
      SolveSpec C hC φ
        (selOrderingRoutine (fun m => bucketSel m)
          (3 * (Headline.headlineSetup C hC φ).R))
        G c₀ w q ext solveCom Ks) ∧
    F7Bridge C hC φ ε ℓp htabF c₀ Ks

/-- **The axiom, verbatim, from the packaged hypothesis.** The only
gap left between this and the endorsed statement is `F7Package` —
`SolveSpec` and the uniform ledger bridge, with the program data that
witnesses them. -/
theorem f7close_modelChecking
    (h : ∀ (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (ε : ℝ),
      0 < ε → F7Package C hC φ ε) :
    F7Goal := by
  intro C hC φ ε hε
  obtain ⟨q, c₀, eS, eA, ext, solveCom, Ks, ℓp, htabF, hq, hokS, hnw,
    hextOff, hextTgt, hsolve, hbr⟩ := h C hC φ ε hε
  exact f7close_exists_of_solveSpec C hC φ ε hε q c₀ eS eA ext solveCom Ks
    ℓp htabF hq hokS hnw hextOff hextTgt hsolve hbr

/-! ## §6 The leaf's axiom profile -/

#print axioms f7_mcD_mono_c

#print axioms f7_solveSpec_mono_c

#print axioms f7_computesInTime_mono

#print axioms ksChargeBridge_of_f7Bridge

#print axioms f7_le_rpow

#print axioms f7close_exists_of_solveSpec

#print axioms f7close_modelChecking

end Lax3Proofs.Prog
