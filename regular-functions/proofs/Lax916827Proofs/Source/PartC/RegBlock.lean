/-
Runs of a two-way transducer confined to one side of a cut of the input, used
by the effective equivalence bound of Theorem `thm:decidable-equivalence-regular`
(`RequestProject/PartC/RegEffBound.lean`).

Fix a cut `n₀` of the input `w`.  A run of a two-way transducer on `w` breaks
into maximal pieces that stay on one side of the cut: a piece on the left uses
only the cuts `0, …, n₀` and ends when a step at the cut `n₀` moves right, and a
piece on the right uses only the cuts `n₀ + 1, …, |w|` and ends when a step at
the cut `n₀ + 1` moves left.  Both are instances of one notion, `Transducers.RegPos.Reg`:
a run that ends either by halting or by the step at a distinguished cut `ex` in a
distinguished direction `dir`.

The point of the confinement is *locality*.  A step at the cut `p` reads only the
letters at the positions `p - 1` and `p`, so a left piece reads only the letters
of the prefix `u` of length `n₀` together with the first letter of the suffix
`v`, and a right piece reads only the letters of `v`.  That is why the two
pieces are described here as runs on two *different* words -- the left ones on
`u ++ v.take 1` and the right ones on `v`, with the cuts shifted by `n₀` -- and
this is what makes the crossing decomposition of
`RequestProject/PartC/RegCross.lean` a decomposition of the value of the run into
a part depending only on `u` and a part depending only on `v`.
-/
import Lax916827Proofs.Source.PartC.RegPos
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegPos

open TwoWay

variable {A B Q : Type}

/-- A run of `M` on `z` that ends either by halting (`none`) or by the step at
the cut `ex` in the direction `dir`, which exits with the state `some q'`.  All
the other steps stay away from that one exit, so such a run is automatically
confined to one side of the cut. -/
inductive Reg (M : TwoWay A B Q) (z : List A) (ex : ℕ) (dir : Bool) :
    ℕ × Q → List B → Option Q → Prop
  | halt {p : ℕ} {q : Q} {o : List B} :
      M.step (leftLet z p) q z[p]? = Sum.inl o → Reg M z ex dir (p, q) o none
  | exit {q q' : Q} {o : List B} :
      M.step (leftLet z ex) q z[ex]? = Sum.inr (q', o, dir) →
      Reg M z ex dir (ex, q) o (some q')
  | moveR {p : ℕ} {q q' : Q} {o o' : List B} {r : Option Q} :
      ¬(p = ex ∧ dir = true) → p < z.length →
      M.step (leftLet z p) q z[p]? = Sum.inr (q', o, true) →
      Reg M z ex dir (p + 1, q') o' r → Reg M z ex dir (p, q) (o ++ o') r
  | moveL {p : ℕ} {q q' : Q} {o o' : List B} {r : Option Q} :
      ¬(p = ex ∧ dir = false) → 0 < p →
      M.step (leftLet z p) q z[p]? = Sum.inr (q', o, false) →
      Reg M z ex dir (p - 1, q') o' r → Reg M z ex dir (p, q) (o ++ o') r

/-- A two-way transducer is deterministic, so a confined run is unique. -/
lemma Reg.det {M : TwoWay A B Q} {z : List A} {ex : ℕ} {dir : Bool} {x : ℕ × Q}
    {o o' : List B} {r r' : Option Q} (h : Reg M z ex dir x o r) (h' : Reg M z ex dir x o' r') :
    o = o' ∧ r = r' := by
  induction h generalizing o' r' with
  | @halt p q o hs =>
      cases h' with
      | halt hs' => rw [hs] at hs'; exact ⟨by simpa using hs', rfl⟩
      | exit hs' => rw [hs] at hs'; simp at hs'
      | moveR _ _ hs' _ => rw [hs] at hs'; simp at hs'
      | moveL _ _ hs' _ => rw [hs] at hs'; simp at hs'
  | @exit q q' o hs =>
      cases h' with
      | halt hs' => rw [hs] at hs'; simp at hs'
      | exit hs' =>
          rw [hs] at hs'
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hs'
          exact ⟨hs'.2.1, by rw [hs'.1]⟩
      | moveR hne _ hs' _ =>
          rw [hs] at hs'
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hs'
          exact absurd ⟨rfl, hs'.2.2 ▸ rfl⟩ hne
      | moveL hne _ hs' _ =>
          rw [hs] at hs'
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hs'
          exact absurd ⟨rfl, hs'.2.2 ▸ rfl⟩ hne
  | @moveR p q q' o o₂ r hne hlt hs _ ih =>
      cases h' with
      | halt hs' => rw [hs] at hs'; simp at hs'
      | exit hs' =>
          rw [hs] at hs'
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hs'
          exact absurd ⟨rfl, hs'.2.2.symm ▸ rfl⟩ hne
      | @moveR _ _ q₂ _ o₃ _ _ _ hs' hrest =>
          rw [hs] at hs'
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hs'
          obtain ⟨hq, ho, -⟩ := hs'
          subst hq; subst ho
          obtain ⟨h1, h2⟩ := ih hrest
          exact ⟨by rw [h1], h2⟩
      | moveL _ _ hs' _ => rw [hs] at hs'; simp at hs'
  | @moveL p q q' o o₂ r hne hpos hs _ ih =>
      cases h' with
      | halt hs' => rw [hs] at hs'; simp at hs'
      | exit hs' =>
          rw [hs] at hs'
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hs'
          exact absurd ⟨rfl, hs'.2.2.symm ▸ rfl⟩ hne
      | moveR _ _ hs' _ => rw [hs] at hs'; simp at hs'
      | @moveL _ _ q₂ _ o₃ _ _ _ hs' hrest =>
          rw [hs] at hs'
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hs'
          obtain ⟨hq, ho, -⟩ := hs'
          subst hq; subst ho
          obtain ⟨h1, h2⟩ := ih hrest
          exact ⟨by rw [h1], h2⟩

/-- A positional run started at the halting vertex is empty. -/
lemma RunP.of_none {M : TwoWay A B Q} {w : List A} {n : ℕ} {o : List B} {y : Option (ℕ × Q)}
    (h : RunP M w n none o y) : o = [] ∧ y = none := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩

end RegPos

end Lax916827Proofs.Transducers
