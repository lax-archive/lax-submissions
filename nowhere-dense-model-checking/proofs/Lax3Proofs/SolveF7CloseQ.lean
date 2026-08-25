import Lax3Proofs.SolveF7Close
import Lax3Proofs.SolveFrameBridge
import Lax3Proofs.SolveMachPrepComp2
import Lax3Proofs.SolveAugRoundIn

/-!
# F7-c, part 2 — every lower bound on `q`, collected, and the budget seam

`q` sizes the value bound `mcB q x = q·(|x|+1)²`, which sits **inside**
`SolveSpec`'s `Spec`, so unlike the axiom's `c` it cannot be raised
after the discharge: `Spec B` is not monotone in `B`. Every constraint
on `q` therefore has to be collected before the machine work, and this
file collects them.

## The four constraints, and where each comes from

1. **`1 ≤ q`** — `ProgCodegenLayout`'s `hinp`/`hfit` (`mcD_entry_lt_mcB`,
   `mcLayout_fitsWords`). Free.
2. **`q ≥ f7qPrep S ℓp hbf`** — `SolveMachPrepComp2.PrepWB` at
   `B = mcB q x`: the prep composition's four word-size clauses, which
   at F7's instantiation are (as that file's docstring predicts) a lower
   bound on the schedule constant and nothing else. `f7prepWB_mcB`
   discharges the whole bundle from `q ≥ f7qPrep` and `x ∈ mcD n G c w`.
3. **`q ≥ f7qB S Kq`** — `solveSpec_closed_scr`'s `hB`: the four bottom
   level figures (`n`, `n·pal ℓ`, `2^{pal ℓ}·(Kq+1)`, `n·|levelFml ℓ|`).
   `f7hB_mcB` discharges it. Note the third is a *constant*, so it
   forces `q` above `2^{pal ℓ}·(Kq+1)` — the single largest term in the
   whole collection, and the one that makes `q` a tower in the
   sentence's quantifier rank. That is expected (`pal` is the isolation
   palette) and it costs nothing in the headline: `q` enters the axiom
   only through `c`, and `c` enters only the *side condition* and the
   time bound's constant, never the exponent.
4. **`q ≥ 3·K + 2`** — `SolveAugRoundIn.ardWordBound_of_inDegLE`, where
   `K` bounds `d(m)² ≤ K·(m+1)` for the selection chain's in-degree
   `d`. §4 produces that `K`: `exists_selChain_inDegLE_pow` at the inner
   exponent `δ' = 1/(2·16^R)` gives `d(m) = (3⌈c₀·m^{δ'}⌉₊+2)^{16^R}`,
   and `δ'·16^R = 1/2` makes `d(m)² = O(m)` exactly. `R` is fixed by the
   setup before `δ'` is chosen, so no circularity: this is the "free"
   the packet describes, made concrete.

`f7q` is the sum of all four, so `q := f7q …` satisfies every one of
them at once and `omega` proves each.

## §5 The budget seam — a finding

`SolveFrameBridge.solveSpec_closed_scr` concludes `SolveSpec` at the
budget

    fun x => matK x + (Krl x + (KB ℓ 0 (rootArena G col) + (Kc + topEvalCost S av)))

which mentions **`G`**. The endorsed axiom's `T` is fixed before `n` and
`G`, and `ProgCodegen.mcK` reads `Ks` as a function of the word alone,
so this budget cannot be handed to `f7close_exists_of_solveSpec`
directly. The repair is not a weakening: `Spec` *is* monotone in its
budget (`Spec.mono`), so `f7_solveSpec_mono_Ks` transports `SolveSpec`
along any pointwise-dominating uniform budget, and
`SolveF7CloseCompose.f7close_of_closed_scr` does exactly that. What the caller
owes is one inequality, `hdom` — a uniform `Ks` above the graph-indexed
budget on every admissible input — which is the same inequality the
ledger bridge already has to prove, at the same place.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver Lax3Proofs.CoverRoutine
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.AugmentedDensity Lax3Proofs.CoverDegree

variable {L : ℕ}

/-! ## §1 The two shapes every clause reduces to -/

/-- An admissible word is at least `n + 3` long — the encoding's own
length identity, which is the only fact about the input any word-size
clause needs. -/
theorem f7_len_ge {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (henc : EncodesGraph x n G) : n + 3 ≤ x.length := by
  have := henc.length_eq; omega

/-- **The constant clause**: any constant below `q` is a word. -/
theorem f7_const_lt_mcB {x : List ℕ} {q a : ℕ} (hq : a + 1 ≤ q) :
    a < mcB q x := by
  have h1 : 1 ≤ (x.length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have : q * 1 ≤ q * (x.length + 1) ^ 2 := Nat.mul_le_mul_left _ h1
  rw [mcB]; omega

/-- **The linear clause**: `n·a` is a word as soon as `q > a`. The
input's length pays for the carrier and `q` for the coefficient. -/
theorem f7_linear_lt_mcB {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    {q a : ℕ} (henc : EncodesGraph x n G) (hq : a + 1 ≤ q) :
    n * a < mcB q x := by
  have hlen := f7_len_ge henc
  have hsq : (n + 4) * (n + 4) ≤ (x.length + 1) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have hstep : (a + 1) * ((n + 4) * (n + 4)) ≤ q * (x.length + 1) ^ 2 :=
    Nat.mul_le_mul hq hsq
  have hlow : n * a + 1 ≤ (a + 1) * ((n + 4) * (n + 4)) := by
    have h1 : (n + 4) ≤ (n + 4) * (n + 4) := Nat.le_mul_of_pos_left _ (by omega)
    calc n * a + 1 ≤ (a + 1) * (n + 4) := by nlinarith
      _ ≤ (a + 1) * ((n + 4) * (n + 4)) := Nat.mul_le_mul_left _ h1
  rw [mcB]; omega

/-! ## §2 Constraint 2 — `PrepWB` at the value bound -/

/-- The prep composition's schedule constant: the largest of the three
`i`-indexed clauses of `PrepWB`, over the levels that exist. -/
noncomputable def f7qPrep (S : Setup L) (ℓp hbf : ℕ → ℕ) : ℕ :=
  1 + (Finset.range (S.depth + 1)).sup (fun i =>
    S.pal (i + 1) + ℓp i * (hbf i + 1)
      + (ℓp i + hbf i + S.width + 2 * S.R + i + 4))

theorem f7qPrep_le (S : Setup L) (ℓp hbf : ℕ → ℕ) {i : ℕ} (hi : i ≤ S.depth) :
    S.pal (i + 1) + ℓp i * (hbf i + 1)
        + (ℓp i + hbf i + S.width + 2 * S.R + i + 4) + 1 ≤ f7qPrep S ℓp hbf := by
  have hmem : i ∈ Finset.range (S.depth + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  have h : S.pal (i + 1) + ℓp i * (hbf i + 1)
      + (ℓp i + hbf i + S.width + 2 * S.R + i + 4)
      ≤ (Finset.range (S.depth + 1)).sup (fun i => S.pal (i + 1) + ℓp i * (hbf i + 1)
          + (ℓp i + hbf i + S.width + 2 * S.R + i + 4)) :=
    Finset.le_sup (f := fun i => S.pal (i + 1) + ℓp i * (hbf i + 1)
      + (ℓp i + hbf i + S.width + 2 * S.R + i + 4)) hmem
  rw [f7qPrep]; omega

/-- **Constraint 2, discharged**: at `q ≥ f7qPrep S ℓp hbf` the prep
composition's whole word-size bundle holds at `B = mcB q x`, on every
admissible input. Exactly as `prepWB_exists`'s docstring predicts, the
bundle is a lower bound on the schedule constant and imposes nothing on
the input. -/
theorem f7prepWB_mcB (S : Setup L) (ℓp hbf : ℕ → ℕ) {n : ℕ}
    {G : SimpleGraph (Fin n)} {c w q : ℕ} (hq : f7qPrep S ℓp hbf ≤ q)
    {x : List ℕ} (hx : x ∈ mcD n G c w) :
    PrepWB S ℓp hbf n (mcB q x) := by
  obtain ⟨henc, -⟩ := hx
  have hq1 : 1 ≤ q := by
    have := f7qPrep_le S ℓp hbf (Nat.zero_le S.depth); omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `n·n + 2n + 3 < B`: the input's own length already pays
    have hlen := f7_len_ge henc
    have hsq : (n + 4) * (n + 4) ≤ (x.length + 1) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
    have : 1 * ((n + 4) * (n + 4)) ≤ q * (x.length + 1) ^ 2 :=
      Nat.mul_le_mul hq1 hsq
    rw [mcB]; nlinarith
  · intro i hi
    have h := f7qPrep_le S ℓp hbf hi
    exact f7_linear_lt_mcB henc (by omega)
  · intro i hi
    have h := f7qPrep_le S ℓp hbf hi
    have : n * ℓp i * (hbf i + 1) = n * (ℓp i * (hbf i + 1)) := by ring
    rw [this]
    exact f7_linear_lt_mcB henc (by omega)
  · intro i hi
    have h := f7qPrep_le S ℓp hbf hi
    exact f7_const_lt_mcB (by omega)

/-! ## §3 Constraint 3 — `solveSpec_closed_scr`'s `hB` -/

/-- The bottom level's schedule constant: the palette stride, the
leaf's constant row block `2^{pal ℓ}·(Kq+1)`, and the level formula
count. -/
noncomputable def f7qB (S : Setup L) (Kq : ℕ) : ℕ :=
  2 + S.pal S.depth + 2 ^ S.pal S.depth * (Kq + 1) + (levelFml S S.depth).length

/-- **Constraint 3, discharged**: `solveSpec_closed_scr`'s `hB`, at
`q ≥ f7qB`. -/
theorem f7hB_mcB (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    {n : ℕ} {G : SimpleGraph (Fin n)} {c w q Kq : ℕ}
    (hq : f7qB (Headline.headlineSetup C hC φ) Kq ≤ q) :
    ∀ x ∈ mcD n G c w,
      n < mcB q x ∧
      n * (Headline.headlineSetup C hC φ).pal
        (Headline.headlineSetup C hC φ).depth < mcB q x ∧
      2 ^ (Headline.headlineSetup C hC φ).pal
        (Headline.headlineSetup C hC φ).depth * (Kq + 1) < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ)
        (Headline.headlineSetup C hC φ).depth).length < mcB q x := by
  rintro x ⟨henc, -⟩
  rw [f7qB] at hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : n * 1 < mcB q x := f7_linear_lt_mcB henc (by omega)
    simpa using h1
  · exact f7_linear_lt_mcB henc (by omega)
  · exact f7_const_lt_mcB (by omega)
  · exact f7_linear_lt_mcB henc (by omega)

/-! ## §4 Constraint 4 — the augmentation round's `K`

`ardWordBound_of_inDegLE` needs a `K` with `d(m)² ≤ K·(m+1)` at every
carrier, where `d` is the selection chain's in-degree bound.
`exists_selChain_inDegLE_pow` supplies `d` at *every* inner exponent
`δ' > 0`; the square is linear exactly when `2·δ'·16^R ≤ 1`, so `δ' :=
1/(2·16^R)` is the choice, and `R` — the setup's radius cap — is fixed
before it. -/

/-- The cast of the raw in-degree bound. (`ProgCoverChargeSel`'s
`selDmax_cast_le` is `private`; this is that statement restated, not new
content.) -/
private theorem f7Dmax_cast_le {c₀ X : ℝ} (hc₀ : 0 ≤ c₀) (hX : 1 ≤ X) (P : ℕ) :
    (((3 * ⌈c₀ * X⌉₊ + 2) ^ P : ℕ) : ℝ) ≤ ((3 * c₀ + 5) * X) ^ P := by
  have hXnn : (0 : ℝ) ≤ X := zero_le_one.trans hX
  have hceil : ((⌈c₀ * X⌉₊ : ℕ) : ℝ) ≤ c₀ * X + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hc₀ hXnn)).le
  have hbase : ((3 * ⌈c₀ * X⌉₊ + 2 : ℕ) : ℝ) ≤ (3 * c₀ + 5) * X := by
    push_cast
    nlinarith [hceil, hX, hc₀]
  calc (((3 * ⌈c₀ * X⌉₊ + 2) ^ P : ℕ) : ℝ)
      = (((3 * ⌈c₀ * X⌉₊ + 2 : ℕ) : ℝ)) ^ P := by push_cast; ring
    _ ≤ ((3 * c₀ + 5) * X) ^ P := by gcongr

/-- **The square of the raw bound is linear** at the inner exponent
`1/(2P)`: with `d m := (3⌈c₀·m^{1/(2P)}⌉₊+2)^P`, there is a `K` with
`d m · d m ≤ K·(m+1)` at every carrier `m`. This is the whole content
of `ardWordBound_of_inDegLE`'s side condition. -/
theorem f7_exists_sq_le_linear {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (P : ℕ) (hP : 0 < P) :
    ∃ K : ℕ, ∀ m : ℕ,
      (3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P
        * (3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P ≤ K * (m + 1) := by
  classical
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hPne : (P : ℝ) ≠ 0 := ne_of_gt hPR
  have hδpos : (0 : ℝ) < 1 / (2 * (P : ℝ)) := by positivity
  have hAnn : (0 : ℝ) ≤ ((3 * c₀ + 5) ^ P) ^ 2 := by positivity
  refine ⟨⌈((3 * c₀ + 5) ^ P) ^ 2⌉₊ + 4 ^ P, fun m => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- the empty carrier: `0 ^ δ = 0`, so the bound is the bare `2 ^ P`
    have h0 : ((0 : ℕ) : ℝ) ^ (1 / (2 * (P : ℝ))) = 0 := by
      rw [Nat.cast_zero]; exact Real.zero_rpow (ne_of_gt hδpos)
    rw [h0, mul_zero, Nat.ceil_zero]
    have h4 : (3 * 0 + 2 : ℕ) ^ P * (3 * 0 + 2 : ℕ) ^ P = 4 ^ P := by
      rw [show (3 * 0 + 2 : ℕ) = 2 from rfl,
        show (4 : ℕ) = 2 * 2 from rfl, Nat.mul_pow]
    omega
  -- a nonempty carrier: cast to `ℝ`, undo the inner exponent
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ (1 / (2 * (P : ℝ))) :=
    Real.one_le_rpow hm1 hδpos.le
  have hcast := f7Dmax_cast_le hc₀ hX1 P
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  -- `((m^δ)^P)^2 = m^(δ·2P) = m`
  have hmul : (1 / (2 * (P : ℝ))) * (((P * 2 : ℕ) : ℝ)) = 1 := by
    push_cast; field_simp
  have hpow : (((m : ℝ) ^ (1 / (2 * (P : ℝ)))) ^ P) ^ 2 = (m : ℝ) := by
    rw [← pow_mul, ← Real.rpow_natCast ((m : ℝ) ^ (1 / (2 * (P : ℝ)))) (P * 2),
      ← Real.rpow_mul hmnn, hmul, Real.rpow_one]
  have hsqR : ((((3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P : ℕ) : ℝ))
      * ((((3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P : ℕ) : ℝ))
      ≤ ((3 * c₀ + 5) ^ P) ^ 2 * (m : ℝ) := by
    have hnn : (0 : ℝ)
        ≤ (((3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hsplit : ((3 * c₀ + 5) * (m : ℝ) ^ (1 / (2 * (P : ℝ)))) ^ P
        * ((3 * c₀ + 5) * (m : ℝ) ^ (1 / (2 * (P : ℝ)))) ^ P
        = ((3 * c₀ + 5) ^ P) ^ 2
          * (((m : ℝ) ^ (1 / (2 * (P : ℝ)))) ^ P) ^ 2 := by
      rw [mul_pow]; ring
    calc ((((3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P : ℕ) : ℝ))
          * ((((3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P : ℕ) : ℝ))
        ≤ ((3 * c₀ + 5) * (m : ℝ) ^ (1 / (2 * (P : ℝ)))) ^ P
            * ((3 * c₀ + 5) * (m : ℝ) ^ (1 / (2 * (P : ℝ)))) ^ P :=
          mul_le_mul hcast hcast hnn (le_trans hnn hcast)
      _ = ((3 * c₀ + 5) ^ P) ^ 2
            * (((m : ℝ) ^ (1 / (2 * (P : ℝ)))) ^ P) ^ 2 := hsplit
      _ = ((3 * c₀ + 5) ^ P) ^ 2 * (m : ℝ) := by rw [hpow]
  -- back to `ℕ`
  have hAle : ((3 * c₀ + 5) ^ P) ^ 2 ≤ ((⌈((3 * c₀ + 5) ^ P) ^ 2⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hcastNat :
      ((((3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P
        * (3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P : ℕ)) : ℝ)
      ≤ (((⌈((3 * c₀ + 5) ^ P) ^ 2⌉₊ * m : ℕ)) : ℝ) := by
    push_cast
    push_cast at hsqR
    exact le_trans hsqR (mul_le_mul_of_nonneg_right hAle hmnn)
  have hnat : (3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P
      * (3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * (P : ℝ)))⌉₊ + 2) ^ P
      ≤ ⌈((3 * c₀ + 5) ^ P) ^ 2⌉₊ * m := by
    exact_mod_cast hcastNat
  exact le_trans hnat
    (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ m))

/-- **Constraint 4, produced**: on a nowhere dense class, at every
radius `R`, there are an in-degree family `d` and a constant `K` such
that every round `i ≤ R` of the selection chain on every subgraph copy
of a member is `InDegLE (d m)`, **and** `d m · d m ≤ K·(m+1)` at every
carrier. `ardWordBound_of_inDegLE` then holds at every `q ≥ 3·K + 2`.

The two halves come from one choice of the inner exponent, and the
choice is legal because `R` is the setup's, fixed before it. -/
theorem f7_exists_selChain_inDegLE_sq (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (R : ℕ) :
    ∃ (d : ℕ → ℕ) (K : ℕ),
      (∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
        ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
          ∀ i ≤ R, (selChain (sel m) G i).InDegLE (d m)) ∧
      (∀ m, d m * d m ≤ K * (m + 1)) := by
  classical
  have hPpos : 0 < (16 ^ R : ℕ) := by positivity
  have hPR : (0 : ℝ) < ((16 ^ R : ℕ) : ℝ) := by exact_mod_cast hPpos
  have hδ' : 0 < 1 / (2 * ((16 ^ R : ℕ) : ℝ)) := by positivity
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_selChain_inDegLE_pow sel C hC R _ hδ'
  obtain ⟨K, hK⟩ := f7_exists_sq_le_linear hc₀0 (16 ^ R) hPpos
  exact ⟨fun m => (3 * ⌈c₀ * (m : ℝ) ^ (1 / (2 * ((16 ^ R : ℕ) : ℝ)))⌉₊ + 2) ^ 16 ^ R,
    K, hc₀, hK⟩

/-! ## §5 The budget seam: `SolveSpec` is monotone in `Ks` -/

/-- **`SolveSpec` transports along a dominating budget** — `Spec.mono`,
lifted. This is what lets F7 replace `solveSpec_closed_scr`'s
graph-indexed budget by one uniform function of the word, which is what
the axiom's `T` requires. -/
theorem f7_solveSpec_mono_Ks (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    {c w q : ℕ} (ext : List ℕ → String → ℕ) (solveCom : Com)
    {Ks Ks' : List ℕ → ℕ}
    (hs : SolveSpec C hC φ ord G c w q ext solveCom Ks)
    (hdom : ∀ x ∈ mcD n G c w, Ks x ≤ Ks' x) :
    SolveSpec C hC φ ord G c w q ext solveCom Ks' :=
  fun x hx => (hs x hx).mono (hdom x hx)

/-! ## §6 The collected constant -/

/-- **Every lower bound on `q`, in one place.** `f7q` is the sum of the
four constraints, so `q := f7q …` satisfies all of them and each
follows by `omega`. -/
noncomputable def f7q (S : Setup L) (ℓp hbf : ℕ → ℕ) (Kq K : ℕ) : ℕ :=
  1 + f7qPrep S ℓp hbf + f7qB S Kq + (3 * K + 2)

theorem f7q_one_le (S : Setup L) (ℓp hbf : ℕ → ℕ) (Kq K : ℕ) :
    1 ≤ f7q S ℓp hbf Kq K := by rw [f7q]; omega

theorem f7q_prep_le (S : Setup L) (ℓp hbf : ℕ → ℕ) (Kq K : ℕ) :
    f7qPrep S ℓp hbf ≤ f7q S ℓp hbf Kq K := by rw [f7q]; omega

theorem f7q_B_le (S : Setup L) (ℓp hbf : ℕ → ℕ) (Kq K : ℕ) :
    f7qB S Kq ≤ f7q S ℓp hbf Kq K := by rw [f7q]; omega

theorem f7q_ard_le (S : Setup L) (ℓp hbf : ℕ → ℕ) (Kq K : ℕ) :
    3 * K + 2 ≤ f7q S ℓp hbf Kq K := by rw [f7q]; omega

/-! ## §7 The leaf's axiom profile -/

#print axioms f7_len_ge

#print axioms f7_const_lt_mcB

#print axioms f7_linear_lt_mcB

#print axioms f7prepWB_mcB

#print axioms f7hB_mcB

#print axioms f7_exists_sq_le_linear

#print axioms f7_exists_selChain_inDegLE_sq

#print axioms f7_solveSpec_mono_Ks

end Lax3Proofs.Prog
