import Lax3Proofs.ProgCodegenParse
import Lax13Proofs.Transfer

/-!
# F6b — the layout, the value bound, and the word-size condition spent

E13 item (d): the endorsed axiom admits inputs with
`c·(x.length + v + 1)² ≤ 2^w` for every entry `v`, and that side
condition must be spent exactly twice on the way to
`computesInTime_of_spec` — as `hinp` (every entry below the value
bound `B x`) and as `hfit` (`Layout.FitsWords (B x) w`: the static
layout's span fits in `2^w` cells). This file does both, against the
skeleton's layout, for the axiom's admissible set **verbatim**.

## The three numbers

* **`mcD n G c w`** — the axiom's own set, verbatim
  (`ModelChecking.lean:122-123`): encodings of `G` whose entries all
  satisfy the squared side condition at constant `c`.
* **`mcB q x := q·(x.length+1)²`** — the value bound, at its own
  constant `q`. Two constants, deliberately: `q` is what the *solve
  stages* need (a constant of the schedule — `Unroll.lean`'s §11
  paragraph prices every stored quantity at `≤ (2+c_S)·n² ≤
  (2+c_S)·(|x|+1)²`, so F7 instantiates `q ≥` that constant), while
  `c` is the axiom's constant, and the axiom lets the prover fix it
  *after* the schedule and before the input. The hypotheses `q ≤ c`
  and `hspan` below are exactly §11's "choose `c` large enough to
  absorb the `ℓ+1` live frames and their constants".
* **`mcLayout eS eA t`** — the parse's nine scalars and two arrays,
  extended by the solve stages' names, over `t` temporaries. The
  extension is a parameter because the Sepref descent owns those
  names; the span arithmetic is closed here once, for every extension,
  through the one inequality `hspan`. `t` is a parameter because
  `Expr.Ok` charges one temporary per level of *left* nesting and the
  root evaluation's compiled boolean combination
  (`SolveMatTop.bcExpr`) nests as deep as the sentence does: at the
  fixed `temps = 2` this file used to carry, `Com.Ok` was
  **unsatisfiable** for the real pipeline
  (`SolveF7CloseCompose.f7_bcExpr_not_ok_at_mcLayout` witnesses it),
  which is the defect this parameter repairs. `t` is fixed with `eS`
  and `eA`, before the input; `SolveF7Temps` computes the value the
  pipeline needs and shows it is a constant of the schedule.

## How the side condition is spent

`2^w ≥ c·(|x| + v + 1)² ≥ c·(|x|+1)²` at any entry `v` (an encoding
has entries — `x.length ≥ 3`), and every entry is `≤ x.length`
(`entry_le_length`). So:

* `hinp` (`mcD_entry_lt_mcB`): `v ≤ |x| < (|x|+1)² ≤ mcB q x` —
  the side condition's *constant* is not even needed here, only
  `1 ≤ q`;
* `B ≤ 2^w` (`mcB_le_two_pow`): `q·(|x|+1)² ≤ c·(|x|+1)² ≤ 2^w`;
* `span ≤ 2^w` (`mcLayout_span_le`): the compiled span is
  `temps + #scalars + #arrays·B = 9 + t + |eS| + (2+|eA|)·q·(|x|+1)²
  ≤ (9 + t + |eS| + (2+|eA|)·q)·(|x|+1)² ≤ c·(|x|+1)² ≤ 2^w` by
  `hspan` — the quadratic side condition paying for the array
  stride, which is the arithmetic reason the axiom's exponent is
  `2` and not `1` (`ModelChecking.lean`'s deviation note). The `9` is
  the parse's scalars and the verdict cell; the `t` is the
  temporaries, and it enters `hspan` **additively**, so raising it
  costs the axiom's constant `c` and nothing else. `Layout.const`
  (`3·idxLen + 13`, `idxLen` counting *arrays*) does not mention
  `temps` at all, so the machine constant — and with it the headline
  exponent — is untouched by the choice of `t`
  (`mcLayout_const_eq`).

`mcLayout_fitsWords` packages the three into `FitsWords`, and is the
`hfit` the skeleton (`ProgCodegen.lean`) feeds to
`computesInTime_of_spec`.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Compile Lax11.GraphEncoding

/-! ## §0 Temporaries

`Expr.Ok L e d` mixes two unrelated conditions: that every name `e`
mentions is in `L`, and that `L` has a temporary for every level of
*left* nesting above `d` (`Expr.Ok L (.bin _ e f) d` asks `d < L.temps`
and recurses into `e` at `d+1`). This section separates them, so that
a `Com.Ok` proof written at one number of temporaries transports to
every larger one, and so that the number an expression needs is a
function of the expression rather than a guess. -/

/-- **`Expr.Ok` is monotone in the layout's temporaries** — the name
clauses do not move, only the depth budgets. -/
theorem expr_ok_mono_temps {L L' : Layout} (hs : L.scalars = L'.scalars)
    (ha : L.arrays = L'.arrays) (ht : L.temps ≤ L'.temps) :
    ∀ (e : Expr) (d : ℕ), Expr.Ok L e d → Expr.Ok L' e d := by
  intro e
  induction e with
  | lit n => intro d _; simp [Expr.Ok]
  | var x => intro d h; simp only [Expr.Ok] at h ⊢; exact hs ▸ h
  | get a i ih =>
    intro d h
    simp only [Expr.Ok] at h ⊢
    exact ⟨ha ▸ h.1, ih d h.2.1, lt_of_lt_of_le h.2.2 ht⟩
  | bin op e f ihe ihf =>
    intro d h
    simp only [Expr.Ok] at h ⊢
    exact ⟨ihf d h.1, ihe (d + 1) h.2.1, lt_of_lt_of_le h.2.2 ht⟩

/-- `Cond.Ok` is monotone in the temporaries. -/
theorem cond_ok_mono_temps {L L' : Layout} (hs : L.scalars = L'.scalars)
    (ha : L.arrays = L'.arrays) (ht : L.temps ≤ L'.temps) (b : Cond) (d : ℕ)
    (h : Cond.Ok L b d) : Cond.Ok L' b d :=
  expr_ok_mono_temps hs ha ht _ d h

/-- **`Com.Ok` is monotone in the temporaries** — the transport that
lets every landed compilability proof be reused at a deeper layout. -/
theorem com_ok_mono_temps {L L' : Layout} (hs : L.scalars = L'.scalars)
    (ha : L.arrays = L'.arrays) (ht : L.temps ≤ L'.temps) :
    ∀ c : Com, Com.Ok L c → Com.Ok L' c := by
  intro c
  induction c with
  | skip => intro _; simp [Com.Ok]
  | assign x e =>
    intro h
    simp only [Com.Ok] at h ⊢
    exact ⟨hs ▸ h.1, expr_ok_mono_temps hs ha ht e 0 h.2⟩
  | store a i e =>
    intro h
    simp only [Com.Ok] at h ⊢
    exact ⟨ha ▸ h.1, expr_ok_mono_temps hs ha ht i 0 h.2.1,
      expr_ok_mono_temps hs ha ht e 1 h.2.2.1,
      lt_of_lt_of_le h.2.2.2 ht⟩
  | seq c d ihc ihd =>
    intro h; simp only [Com.Ok] at h ⊢; exact ⟨ihc h.1, ihd h.2⟩
  | ite b c d ihc ihd =>
    intro h
    simp only [Com.Ok] at h ⊢
    exact ⟨cond_ok_mono_temps hs ha ht b 0 h.1, ihc h.2.1, ihd h.2.2⟩
  | «while» b c ihc =>
    intro h
    simp only [Com.Ok] at h ⊢
    exact ⟨cond_ok_mono_temps hs ha ht b 0 h.1, ihc h.2⟩
  | read x => intro h; simp only [Com.Ok] at h ⊢; exact hs ▸ h
  | write e =>
    intro h
    simp only [Com.Ok] at h ⊢
    exact ⟨expr_ok_mono_temps hs ha ht e 0 h.1, lt_of_lt_of_le h.2 ht⟩

/-- **The temporaries an expression needs**, counted at depth `0`: one
per level of *left* nesting, and one for any array read at all. This is
a function of the expression alone — no layout, no input — which is the
whole reason a `temps` big enough for the pipeline can be fixed before
the input exists. -/
def exprTemps : Expr → ℕ
  | .lit _ => 0
  | .var _ => 0
  | .get _ i => max (exprTemps i) 1
  | .bin _ e f => max (exprTemps f) (exprTemps e + 1)

@[simp] theorem exprTemps_lit (n : ℕ) : exprTemps (.lit n) = 0 := rfl

@[simp] theorem exprTemps_var (x : String) : exprTemps (.var x) = 0 := rfl

@[simp] theorem exprTemps_get (a : String) (i : Expr) :
    exprTemps (.get a i) = max (exprTemps i) 1 := rfl

@[simp] theorem exprTemps_bin (op : Bop) (e f : Expr) :
    exprTemps (.bin op e f) = max (exprTemps f) (exprTemps e + 1) := rfl

/-- The names an expression mentions are all in the layout — the half
of `Expr.Ok` that has nothing to do with temporaries. -/
def ExprNamesOk (L : Layout) : Expr → Prop
  | .lit _ => True
  | .var x => x ∈ L.scalars
  | .get a i => a ∈ L.arrays ∧ ExprNamesOk L i
  | .bin _ e f => ExprNamesOk L e ∧ ExprNamesOk L f

/-- **`Expr.Ok`, from the two halves**: the names, and enough
temporaries for the nesting the expression has above `d`. -/
theorem expr_ok_of_exprTemps {L : Layout} :
    ∀ (e : Expr) (d : ℕ), ExprNamesOk L e → d + exprTemps e ≤ L.temps →
      Expr.Ok L e d := by
  intro e
  induction e with
  | lit n => intro d _ _; simp [Expr.Ok]
  | var x => intro d hn _; simpa [Expr.Ok] using hn
  | get a i ih =>
    intro d hn ht
    simp only [ExprNamesOk] at hn
    simp only [exprTemps_get] at ht
    exact ⟨hn.1, ih d hn.2 (by omega), by omega⟩
  | bin op e f ihe ihf =>
    intro d hn ht
    simp only [ExprNamesOk] at hn
    simp only [exprTemps_bin] at ht
    exact ⟨ihf d hn.2 (by omega), ihe (d + 1) hn.1 (by omega), by omega⟩

/-! ## §1 The three numbers -/

/-- **The static layout**: the front end's cells (`parseScalars` and
the verdict cell) and its two arrays, extended by the solve stages'
scalar and array names, over `t` temporaries.

`t` is a parameter and not the fixed `2` this definition used to carry.
`Expr.Ok` charges one temporary per level of left nesting, and the root
evaluation compiles the sentence's whole boolean combination into one
left-nested expression, so `2` makes `Com.Ok` unsatisfiable for the
real pipeline — the defect `SolveF7CloseCompose.f7_bcExpr_not_ok_at_mcLayout`
witnesses. `t` is fixed with `eS` and `eA`, before `n`, `G` and the
input; `SolveF7Temps.f7Temps` is the value the pipeline needs and is a
function of the schedule and the compiled read expressions alone. -/
def mcLayout (eS eA : List String) (t : ℕ) : Layout :=
  ⟨["n", "m", "np1", "mm", "i", "t", "j", "u", "verdict"] ++ eS,
    ["off", "tgt"] ++ eA, t⟩

@[simp] theorem mcLayout_temps (eS eA : List String) (t : ℕ) :
    (mcLayout eS eA t).temps = t := rfl

@[simp] theorem mcLayout_scalars (eS eA : List String) (t : ℕ) :
    (mcLayout eS eA t).scalars =
      ["n", "m", "np1", "mm", "i", "t", "j", "u", "verdict"] ++ eS := rfl

@[simp] theorem mcLayout_arrays (eS eA : List String) (t : ℕ) :
    (mcLayout eS eA t).arrays = ["off", "tgt"] ++ eA := rfl

/-- **The machine constant does not see the temporaries.**
`Layout.const = 3·idxLen + 13` and `idxLen` counts *arrays*, so the
whole `temps` parameter is free at the cost level: the compiled
program's step constant, and with it the headline exponent, is the same
at every `t`. -/
theorem mcLayout_const_eq (eS eA : List String) (t t' : ℕ) :
    (mcLayout eS eA t).const = (mcLayout eS eA t').const := rfl

/-- The verdict cell is a scalar of every instantiation — the name half
of the root evaluation's `Com.Ok`. -/
theorem mcLayout_verdict_mem (eS eA : List String) (t : ℕ) :
    "verdict" ∈ (mcLayout eS eA t).scalars := by simp

/-- Deepening the layout preserves compilability. -/
theorem mcLayout_com_ok_mono {eS eA : List String} {t t' : ℕ} (ht : t ≤ t')
    {c : Com} (h : Com.Ok (mcLayout eS eA t) c) : Com.Ok (mcLayout eS eA t') c :=
  com_ok_mono_temps (L := mcLayout eS eA t) (L' := mcLayout eS eA t') rfl rfl ht c h

/-- **The admissible inputs — the endorsed axiom's set, verbatim**
(`concepts/Lax3/ModelChecking.lean:122-123`): CSR encodings of `G`
each of whose entries `v` satisfies `c·(x.length + v + 1)² ≤ 2^w`. -/
def mcD (n : ℕ) (G : SimpleGraph (Fin n)) (c w : ℕ) : Set (List ℕ) :=
  {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ 2 ≤ 2 ^ w}

/-- **The value bound**: `q·(|x|+1)²`. Quadratic because the solve
stages store `n²`-sized quantities (`Unroll.lean` §11: the cover
output and the arena both weigh up to `n² ≤ (|x|+1)²` per frame); `q`
is the schedule's constant, fixed by F7's instantiation. -/
def mcB (q : ℕ) (x : List ℕ) : ℕ := q * (x.length + 1) ^ 2

variable {n : ℕ} {G : SimpleGraph (Fin n)} {c w q : ℕ}

/-! ## §2 Small arithmetic about the bound -/

theorem length_add_one_lt_mcB {x : List ℕ} (h3 : 3 ≤ x.length) (hq : 1 ≤ q) :
    x.length + 1 < mcB q x := by
  have hsq : (x.length + 1) * 4 ≤ (x.length + 1) * (x.length + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have : (x.length + 1) * (x.length + 1) ≤ mcB q x := by
    rw [mcB, pow_two]
    exact Nat.le_mul_of_pos_left _ hq
  omega

theorem one_lt_mcB {x : List ℕ} (h3 : 3 ≤ x.length) (hq : 1 ≤ q) : 1 < mcB q x := by
  have := length_add_one_lt_mcB h3 hq
  omega

/-- An encoding is nonempty — so the side condition, quantified over
its entries, is never vacuous. -/
theorem encodesGraph_ne_nil {x : List ℕ} (henc : EncodesGraph x n G) : x ≠ [] := by
  intro h
  have hl := henc.length_eq
  rw [h] at hl
  simp only [List.length_nil] at hl
  omega

/-- The side condition at any one entry already bounds the *entry-free*
quadratic: `c·(|x|+1)² ≤ 2^w`. -/
theorem c_mul_sq_le_two_pow : ∀ x ∈ mcD n G c w,
    c * (x.length + 1) ^ 2 ≤ 2 ^ w := by
  rintro x ⟨henc, hside⟩
  have hne : x ≠ [] := encodesGraph_ne_nil henc
  have hv := hside (x.head hne) (List.head_mem hne)
  calc c * (x.length + 1) ^ 2
      ≤ c * (x.length + x.head hne + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ ≤ 2 ^ w := hv

/-! ## §3 The two halves of item (d) -/

/-- **`hinp`, discharged**: every entry of an admissible word is below
the value bound — `entry_le_length` (every entry is at most the word's
length) against `|x| < mcB q x`. -/
theorem mcD_entry_lt_mcB (hq : 1 ≤ q) :
    ∀ x ∈ mcD n G c w, ∀ v ∈ x, v < mcB q x := by
  rintro x ⟨henc, -⟩ v hv
  have h1 := entry_le_length henc v hv
  have h2 := length_add_one_lt_mcB (three_le_length henc) hq
  omega

/-- The bound fits the word: `mcB q x ≤ 2^w`, from `q ≤ c` and the
side condition. -/
theorem mcB_le_two_pow (hqc : q ≤ c) :
    ∀ x ∈ mcD n G c w, mcB q x ≤ 2 ^ w := fun x hx =>
  le_trans (Nat.mul_le_mul_right _ hqc) (c_mul_sq_le_two_pow x hx)

/-- The span fits the word: the compiled layout addresses
`9 + t + |eS| + (2+|eA|)·mcB q x` cells, and `hspan` folds the whole
constant — the nine parse scalars, the `t` temporaries and the array
stride — under the side condition's `c`. The temporaries enter
additively, which is the whole cost of the `temps` parameter. -/
theorem mcLayout_span_le (eS eA : List String) (t : ℕ)
    (hspan : 9 + t + eS.length + (2 + eA.length) * q ≤ c) :
    ∀ x ∈ mcD n G c w, (mcLayout eS eA t).span (mcB q x) ≤ 2 ^ w := by
  intro x hx
  have hs1 : 1 ≤ (x.length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hlay : (mcLayout eS eA t).span (mcB q x)
      = 9 + t + eS.length + (2 + eA.length) * (q * (x.length + 1) ^ 2) := by
    simp only [mcLayout, Layout.span, List.length_append, List.length_cons,
      List.length_nil, mcB]
    ring
  have hle : 9 + t + eS.length + (2 + eA.length) * (q * (x.length + 1) ^ 2)
      ≤ (9 + t + eS.length + (2 + eA.length) * q) * (x.length + 1) ^ 2 :=
    calc 9 + t + eS.length + (2 + eA.length) * (q * (x.length + 1) ^ 2)
        ≤ (9 + t + eS.length) * (x.length + 1) ^ 2
            + (2 + eA.length) * q * (x.length + 1) ^ 2 :=
          Nat.add_le_add (Nat.le_mul_of_pos_right _ (by omega))
            (le_of_eq (mul_assoc _ _ _).symm)
      _ = (9 + t + eS.length + (2 + eA.length) * q) * (x.length + 1) ^ 2 := by ring
  calc (mcLayout eS eA t).span (mcB q x)
      = 9 + t + eS.length + (2 + eA.length) * (q * (x.length + 1) ^ 2) := hlay
    _ ≤ (9 + t + eS.length + (2 + eA.length) * q) * (x.length + 1) ^ 2 := hle
    _ ≤ c * (x.length + 1) ^ 2 := Nat.mul_le_mul_right _ hspan
    _ ≤ 2 ^ w := c_mul_sq_le_two_pow x hx

/-- **`hfit`, discharged — the word-size side condition, spent**
(E13 item (d)): on every admissible input the layout runs at word
length `w` under the bound `mcB q x`. The three hypotheses are the
whole of what F7's instantiation owes this file: `1 ≤ q ≤ c` and one
inequality folding the layout's constants under the axiom's `c` —
`Unroll.lean` §11's "choose `c` large enough to absorb the `ℓ+1`
live frames and their constants", as one line. -/
theorem mcLayout_fitsWords (eS eA : List String) (t : ℕ)
    (hq : 1 ≤ q) (hqc : q ≤ c)
    (hspan : 9 + t + eS.length + (2 + eA.length) * q ≤ c) :
    ∀ x ∈ mcD n G c w, (mcLayout eS eA t).FitsWords (mcB q x) w := by
  intro x hx
  obtain ⟨henc, hside⟩ := hx
  exact ⟨one_lt_mcB (three_le_length henc) hq,
    mcB_le_two_pow hqc x ⟨henc, hside⟩,
    mcLayout_span_le eS eA t hspan x ⟨henc, hside⟩⟩

end Lax3Proofs.Prog
