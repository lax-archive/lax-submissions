/-
The pieces of the crossing decomposition of
`RequestProject/PartC/RegCross.lean`, read off from the two sides of the cut.

The decomposition `Transducers.RegPos.Alt` says that the output of a halting run
splits along a crossing sequence `cs : List Q`.  What the Hankel decomposition of
`RequestProject/PartC/RegHankel.lean` needs is the converse reading: given a
*candidate* crossing sequence `cs`, the entry point of its `i`-th piece is
determined by `cs` and `i` alone (`Transducers.RegPos.entryC`), so the assertion
that `cs` is the crossing sequence of the run splits into a condition on the
left pieces -- which depend only on the prefix `u` of the input and on the first
letter of the suffix -- and a condition on the right pieces, which depend only
on the suffix `v`.

`Transducers.RegPos.Alt.blk_eq` proves that the true crossing sequence satisfies
both conditions and that the output is the concatenation of the pieces, and
`Transducers.RegPos.alt_of_blkRes` proves the converse, so that by the uniqueness
of the decomposition a candidate satisfying both conditions *is* the true
crossing sequence.
-/
import Lax916827Proofs.Source.PartC.RegCross
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegPos

open TwoWay

variable {A B Q : Type}

/-! ## The output and the outcome of a confined run -/

open Classical in
/-- The outcome of the confined run starting at `x`: `some none` if it halts,
`some (some q')` if it exits in the state `q'`, and `none` if there is no such
run. -/
noncomputable def regRes (M : TwoWay A B Q) (z : List A) (ex : ℕ) (dir : Bool) (x : ℕ × Q) :
    Option (Option Q) :=
  if h : ∃ (o : List B) (r : Option Q), Reg M z ex dir x o r then some h.choose_spec.choose
  else none

open Classical in
/-- The output of the confined run starting at `x`. -/
noncomputable def regOut (M : TwoWay A B Q) (z : List A) (ex : ℕ) (dir : Bool) (x : ℕ × Q) :
    List B :=
  if h : ∃ (o : List B) (r : Option Q), Reg M z ex dir x o r then h.choose else []

lemma regOut_regRes {M : TwoWay A B Q} {z : List A} {ex : ℕ} {dir : Bool} {x : ℕ × Q}
    {o : List B} {r : Option Q} (hr : Reg M z ex dir x o r) :
    regOut M z ex dir x = o ∧ regRes M z ex dir x = some r := by
  classical
  have h : ∃ (o : List B) (r : Option Q), Reg M z ex dir x o r := ⟨o, r, hr⟩
  have hspec : Reg M z ex dir x h.choose h.choose_spec.choose := h.choose_spec.choose_spec
  obtain ⟨h1, h2⟩ := Reg.det hspec hr
  constructor
  · rw [regOut, dif_pos h, h1]
  · rw [regRes, dif_pos h, h2]

lemma exists_reg_of_regRes {M : TwoWay A B Q} {z : List A} {ex : ℕ} {dir : Bool} {x : ℕ × Q}
    {r : Option Q} (h : regRes M z ex dir x = some r) : ∃ o, Reg M z ex dir x o r := by
  classical
  rw [regRes] at h
  split at h
  · next hex =>
      refine ⟨hex.choose, ?_⟩
      have := hex.choose_spec.choose_spec
      rwa [Option.some.inj h] at this
  · exact absurd h (by simp)

/-! ## The pieces, indexed by the side of the cut -/

open Classical in
/-- The outcome of the piece of the run on the side `side` starting at `x`. -/
noncomputable def blkRes (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    Bool → ℕ × Q → Option (Option Q)
  | true => regRes M z n₀ true
  | false => regRes M v 1 false

open Classical in
/-- The output of the piece of the run on the side `side` starting at `x`. -/
noncomputable def blkOut (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    Bool → ℕ × Q → List B
  | true => regOut M z n₀ true
  | false => regOut M v 1 false

@[simp] lemma blkRes_true (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    blkRes M z v n₀ true = regRes M z n₀ true := rfl

@[simp] lemma blkRes_false (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    blkRes M z v n₀ false = regRes M v 1 false := rfl

@[simp] lemma blkOut_true (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    blkOut M z v n₀ true = regOut M z n₀ true := rfl

@[simp] lemma blkOut_false (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    blkOut M z v n₀ false = regOut M v 1 false := rfl

lemma blkOut_blkRes {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} {side : Bool} {x : ℕ × Q}
    {o : List B} {r : Option Q} (hr : Blk M z v n₀ side x o r) :
    blkOut M z v n₀ side x = o ∧ blkRes M z v n₀ side x = some r := by
  cases side with
  | true => exact regOut_regRes hr
  | false => exact regOut_regRes hr

lemma exists_blk_of_blkRes {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} {side : Bool} {x : ℕ × Q}
    {r : Option Q} (h : blkRes M z v n₀ side x = some r) : ∃ o, Blk M z v n₀ side x o r := by
  cases side with
  | true => exact exists_reg_of_regRes h
  | false => exact exists_reg_of_regRes h

/-! ## The entry point of a piece -/

/-- The entry point of the `i`-th piece of a decomposition with crossing
sequence `cs` that starts on the side `side` at `x0`. -/
def entryC (init : Q) (n₀ : ℕ) (side : Bool) (x0 : ℕ × Q) (cs : List Q) (i : ℕ) : ℕ × Q :=
  if i = 0 then x0 else nxt n₀ (!(flipn side i)) (cs.getD (i - 1) init)

@[simp] lemma entryC_zero (init : Q) (n₀ : ℕ) (side : Bool) (x0 : ℕ × Q) (cs : List Q) :
    entryC init n₀ side x0 cs 0 = x0 := by simp [entryC]

lemma entryC_succ (init : Q) (n₀ : ℕ) (side : Bool) (x0 : ℕ × Q) (cs : List Q) (i : ℕ) :
    entryC init n₀ side x0 cs (i + 1) = nxt n₀ (!(flipn side (i + 1))) (cs.getD i init) := by
  simp [entryC]

/-- The entry points of the pieces after the first one are those of the
decomposition that starts with the second piece. -/
lemma entryC_shift (init : Q) (n₀ : ℕ) (side : Bool) (x0 : ℕ × Q) (q' : Q) (cs : List Q) (i : ℕ) :
    entryC init n₀ (!side) (nxt n₀ side q') cs i = entryC init n₀ side x0 (q' :: cs) (i + 1) := by
  cases i with
  | zero => simp [entryC]
  | succ k =>
      rw [entryC_succ, entryC_succ]
      simp [flipn_not]

lemma flipn_shift (side : Bool) (i : ℕ) : flipn (!side) i = flipn side (i + 1) := by
  rw [flipn_not, flipn_succ]

/-! ## The two readings of the decomposition -/

/-- **The pieces of the true decomposition.**  If the output of a run splits
along the crossing sequence `cs`, then the piece entered at the `i`-th entry
point exits with the `i`-th state of `cs` (or halts, at the last piece), and the
output is the concatenation of the pieces. -/
lemma Alt.blk_eq {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} {side : Bool} {x0 : ℕ × Q}
    {cs : List Q} {o : List B} (init : Q) (h : Alt M z v n₀ side x0 cs o) :
    (∀ i ≤ cs.length,
        blkRes M z v n₀ (flipn side i) (entryC init n₀ side x0 cs i) = some cs[i]?) ∧
      o = ((List.range (cs.length + 1)).map
        (fun i => blkOut M z v n₀ (flipn side i) (entryC init n₀ side x0 cs i))).flatten := by
  induction h with
  | @halt side x0 ob hb =>
      constructor
      · intro i hi
        obtain rfl : i = 0 := by simpa using hi
        simpa using (blkOut_blkRes hb).2
      · simpa using (blkOut_blkRes hb).1.symm
  | @cont side x0 ob o₁ q' cs hb hrest ih =>
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      · intro i hi
        cases i with
        | zero => simpa using (blkOut_blkRes hb).2
        | succ k =>
            have hk : k ≤ cs.length := by simpa using hi
            have := ih1 k hk
            rw [entryC_shift init n₀ side x0 q' cs k, flipn_shift] at this
            simpa using this
      · rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.flatten_cons, List.map_map]
        simp only [flipn_zero, entryC_zero]
        rw [(blkOut_blkRes hb).1]
        congr 1
        rw [ih2]
        congr 1
        refine List.map_congr_left ?_
        intro k _
        simp only [Function.comp_apply]
        rw [entryC_shift init n₀ side x0 q' cs k, flipn_shift]

/-- **A candidate crossing sequence whose pieces fit is a real one.**  This is
the converse of `Transducers.RegPos.Alt.blk_eq`; with the uniqueness of the
decomposition it says that the two conditions -- one on the left pieces, one on
the right pieces -- pin the crossing sequence down. -/
lemma alt_of_blkRes {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} (init : Q) :
    ∀ (cs : List Q) (side : Bool) (x0 : ℕ × Q),
      (∀ i ≤ cs.length,
        blkRes M z v n₀ (flipn side i) (entryC init n₀ side x0 cs i) = some cs[i]?) →
      ∃ o, Alt M z v n₀ side x0 cs o := by
  intro cs
  induction cs with
  | nil =>
      intro side x0 hOK
      obtain ⟨o, ho⟩ := exists_blk_of_blkRes (by simpa using hOK 0 (by simp))
      exact ⟨o, Alt.halt ho⟩
  | cons q' cs ih =>
      intro side x0 hOK
      obtain ⟨ob, hob⟩ := exists_blk_of_blkRes (r := some q') (by simpa using hOK 0 (by simp))
      have hOK' : ∀ i ≤ cs.length,
          blkRes M z v n₀ (flipn (!side) i) (entryC init n₀ (!side) (nxt n₀ side q') cs i)
            = some cs[i]? := by
        intro i hi
        have h2 := hOK (i + 1) (by simpa using hi)
        rw [← entryC_shift init n₀ side x0 q' cs i, ← flipn_shift] at h2
        simpa using h2
      obtain ⟨o₁, ho₁⟩ := ih (!side) (nxt n₀ side q') hOK'
      exact ⟨ob ++ o₁, Alt.cont hob ho₁⟩

end RegPos

end Lax916827Proofs.Transducers
