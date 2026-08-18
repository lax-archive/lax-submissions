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
* **`mcLayout eS eA`** — the parse's nine scalars and two arrays,
  extended by the solve stages' names. The extension is a parameter
  because the Sepref descent owns those names; the span arithmetic
  is closed here once, for every extension, through the one
  inequality `hspan`.

## How the side condition is spent

`2^w ≥ c·(|x| + v + 1)² ≥ c·(|x|+1)²` at any entry `v` (an encoding
has entries — `x.length ≥ 3`), and every entry is `≤ x.length`
(`entry_le_length`). So:

* `hinp` (`mcD_entry_lt_mcB`): `v ≤ |x| < (|x|+1)² ≤ mcB q x` —
  the side condition's *constant* is not even needed here, only
  `1 ≤ q`;
* `B ≤ 2^w` (`mcB_le_two_pow`): `q·(|x|+1)² ≤ c·(|x|+1)² ≤ 2^w`;
* `span ≤ 2^w` (`mcLayout_span_le`): the compiled span is
  `temps + #scalars + #arrays·B = 11 + |eS| + (2+|eA|)·q·(|x|+1)²
  ≤ (11 + |eS| + (2+|eA|)·q)·(|x|+1)² ≤ c·(|x|+1)² ≤ 2^w` by
  `hspan` — the quadratic side condition paying for the array
  stride, which is the arithmetic reason the axiom's exponent is
  `2` and not `1` (`ModelChecking.lean`'s deviation note).

`mcLayout_fitsWords` packages the three into `FitsWords`, and is the
`hfit` the skeleton (`ProgCodegen.lean`) feeds to
`computesInTime_of_spec`.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Compile Lax11.GraphEncoding

/-! ## §1 The three numbers -/

/-- **The static layout**: the front end's cells (`parseScalars` and
the verdict cell) and its two arrays, extended by the solve stages'
scalar and array names. Two temporaries — the depth the parse's and
the epilogue's expressions need; a solve stage needing deeper
expression nesting extends the base the same way (a bigger `temps`
only shifts the constant in `hspan`). -/
def mcLayout (eS eA : List String) : Layout :=
  ⟨["n", "m", "np1", "mm", "i", "t", "j", "u", "verdict"] ++ eS,
    ["off", "tgt"] ++ eA, 2⟩

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
`11 + |eS| + (2+|eA|)·mcB q x` cells, and `hspan` folds the whole
constant under the side condition's `c`. -/
theorem mcLayout_span_le (eS eA : List String)
    (hspan : 11 + eS.length + (2 + eA.length) * q ≤ c) :
    ∀ x ∈ mcD n G c w, (mcLayout eS eA).span (mcB q x) ≤ 2 ^ w := by
  intro x hx
  have hs1 : 1 ≤ (x.length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hlay : (mcLayout eS eA).span (mcB q x)
      = 11 + eS.length + (2 + eA.length) * (q * (x.length + 1) ^ 2) := by
    simp only [mcLayout, Layout.span, List.length_append, List.length_cons,
      List.length_nil, mcB]
    ring
  have hle : 11 + eS.length + (2 + eA.length) * (q * (x.length + 1) ^ 2)
      ≤ (11 + eS.length + (2 + eA.length) * q) * (x.length + 1) ^ 2 :=
    calc 11 + eS.length + (2 + eA.length) * (q * (x.length + 1) ^ 2)
        ≤ (11 + eS.length) * (x.length + 1) ^ 2
            + (2 + eA.length) * q * (x.length + 1) ^ 2 :=
          Nat.add_le_add (Nat.le_mul_of_pos_right _ (by omega))
            (le_of_eq (mul_assoc _ _ _).symm)
      _ = (11 + eS.length + (2 + eA.length) * q) * (x.length + 1) ^ 2 := by ring
  calc (mcLayout eS eA).span (mcB q x)
      = 11 + eS.length + (2 + eA.length) * (q * (x.length + 1) ^ 2) := hlay
    _ ≤ (11 + eS.length + (2 + eA.length) * q) * (x.length + 1) ^ 2 := hle
    _ ≤ c * (x.length + 1) ^ 2 := Nat.mul_le_mul_right _ hspan
    _ ≤ 2 ^ w := c_mul_sq_le_two_pow x hx

/-- **`hfit`, discharged — the word-size side condition, spent**
(E13 item (d)): on every admissible input the layout runs at word
length `w` under the bound `mcB q x`. The three hypotheses are the
whole of what F7's instantiation owes this file: `1 ≤ q ≤ c` and one
inequality folding the layout's constants under the axiom's `c` —
`Unroll.lean` §11's "choose `c` large enough to absorb the `ℓ+1`
live frames and their constants", as one line. -/
theorem mcLayout_fitsWords (eS eA : List String)
    (hq : 1 ≤ q) (hqc : q ≤ c)
    (hspan : 11 + eS.length + (2 + eA.length) * q ≤ c) :
    ∀ x ∈ mcD n G c w, (mcLayout eS eA).FitsWords (mcB q x) w := by
  intro x hx
  obtain ⟨henc, hside⟩ := hx
  exact ⟨one_lt_mcB (three_le_length henc) hq,
    mcB_le_two_pow hqc x ⟨henc, hside⟩,
    mcLayout_span_le eS eA hspan x ⟨henc, hside⟩⟩

end Lax3Proofs.Prog
