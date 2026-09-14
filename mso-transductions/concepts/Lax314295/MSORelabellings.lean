import Lax314295.MSOLogic

/-!
---
title: MSO relabellings
type: definition
---
An *mso relabelling* (Definition C.4.3 of *Transducers*) consists of an input
alphabet $A$, an output alphabet $B$, a finite set $\Phi$ of mso formulas over
$A$ each with exactly one free first-order variable, an output map
$\Phi \to B^*$, and a string in $B^*$ for the empty input, such that for every
input string and every position in it exactly one formula of $\Phi$ is true at
that position. The relabelling maps a nonempty input to the concatenation, over
its positions, of the outputs of the unique formulas true there, and the empty
input to the designated string. MSO relabellings define exactly the rational
functions (Theorem C.4.4), and *first-order relabellings* — all of whose
formulas are first-order — exactly the functions of aperiodic bimachines
(Theorem C.4.16).

# Formalization notes

The set of formulas is indexed by a finite type `Idx`; the free variable of every
formula is the variable `0`, and a formula is evaluated at a position `p` under
the valuation sending every variable to `p`. `Relabels R w v` is the graph of
the relabelling, uniqueness of the true formula being a field of the structure.
-/

namespace Lax314295.MSORelabellings

open Lax314295.MSOLogic

/-- An mso relabelling: a finite family of formulas with one free first-order
variable (the variable `0`), exactly one of which holds at each position of each
input, an output string for each formula, and an output for the empty input. -/
structure MSORelabelling (A B : Type) where
  /-- The index set of the formulas. -/
  Idx : Type
  /-- Finiteness of the index set. -/
  finIdx : Finite Idx
  /-- The formulas, each with the one free first-order variable `x₀`. -/
  form : Idx → MSO A
  /-- The output string of each formula. -/
  out : Idx → List B
  /-- The output string for the empty input. -/
  emptyOut : List B
  /-- At every position of every input string exactly one formula holds. -/
  unique : ∀ (w : List A) (p : ℕ), p < w.length →
    ∃! i : Idx, MSO.Sat w (fun _ => p) (fun _ => ∅) (form i)

namespace MSORelabelling

variable {A B : Type}

/-- The relabelling maps `w` to `v`: for a nonempty input, `v` is the concatenation
of the outputs of the formulas true at the positions of `w`; the empty input
gives the designated string. -/
def Relabels (R : MSORelabelling A B) (w : List A) (v : List B) : Prop :=
  (w = [] ∧ v = R.emptyOut) ∨
  (w ≠ [] ∧ ∃ g : ℕ → R.Idx,
    (∀ p < w.length, MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form (g p))) ∧
    v = ((List.range w.length).map (fun p => R.out (g p))).flatten)

/-- All formulas of the relabelling are first-order. -/
def AllFO (R : MSORelabelling A B) : Prop := ∀ i, (R.form i).IsFO

end MSORelabelling

/-- A function defined by an mso relabelling. -/
def IsMSORelabelling {A B : Type} (f : List A → List B) : Prop :=
  ∃ R : MSORelabelling A B, ∀ w, R.Relabels w (f w)

/-- A function defined by a first-order relabelling. -/
def IsFORelabelling {A B : Type} (f : List A → List B) : Prop :=
  ∃ R : MSORelabelling A B, R.AllFO ∧ ∀ w, R.Relabels w (f w)

end Lax314295.MSORelabellings
