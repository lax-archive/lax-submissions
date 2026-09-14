import Lax314295.MSOLogic

/-!
---
title: String-to-string MSO transductions
type: definition
---
A *string-to-string mso transduction* (Definition C.4.7 of *Transducers*) is
given by an input alphabet $A$, an output alphabet $B$, a linear type
$\tau = k \cdot n + c$ — on an input of length $n$ it has $k$ copies of each
input position and $c$ extra elements — and mso formulas over $A$: a *universe
formula* $\varphi_{\mathrm{univ}}(x : \tau)$, a *letter formula*
$\varphi_b(x : \tau)$ for each $b \in B$, and an *order formula*
$\varphi_\le(x : \tau, y : \tau)$. It is required that for every input, every
element selected by the universe formula satisfies exactly one letter formula
and the order formula is a linear order on the selected elements. The output on
$w$ is then the string obtained by taking the selected elements of $\tau(w)$,
ordering them by the order formula and labelling them by the letter formulas.
Linearity of $\tau$ keeps the output of linear size; string-to-string mso
transductions define exactly the regular functions (Theorem C.4.8).

# Formalization notes

A variable of the linear type $\tau = k \cdot n + c$ is a case distinction over
its $k + c$ variants, so the formulas are given per variant: `univP i` and
`labP i b` with the free variable `x₀` for the copies of the positions,
sentences `univC j`, `labC j b` for the extra elements, and four families of
order formulas according to the variants of the two arguments, with free
variables `x₀, x₁`. The elements of $\tau(w)$ are `Elt = (Fin copies × ℕ) ⊕ Fin
extra`, `selected` those chosen by the universe formulas, `ordRel` and `labRel`
the relations defined by the order and letter formulas, and `Outputs T w v`
says that `v` lists the selected elements in the order, with their letters.
`Proper` is the requirement of the definition — exactly one letter formula per
selected element, and a linear order (reflexive, antisymmetric, transitive,
total) on the selected elements; without it every length preserving function
would be a transduction and Theorem C.4.8 would fail, so it is part of
`IsMSOTransduction`.
-/

namespace Lax314295.MSOTransductions

open Lax314295.MSOLogic

/-- A string-to-string mso transduction of the linear type `copies · n + extra`,
presented by families of ordinary mso formulas indexed by the variants of the
type. -/
structure MSOTransduction (A B : Type) where
  /-- The number of copies of the input positions. -/
  copies : ℕ
  /-- The number of extra (constant) elements. -/
  extra : ℕ
  /-- Universe formulas for the copies of the positions; free variable `x₀`. -/
  univP : Fin copies → MSO A
  /-- Universe formulas for the extra elements; sentences. -/
  univC : Fin extra → MSO A
  /-- Letter formulas for the copies of the positions; free variable `x₀`. -/
  labP : Fin copies → B → MSO A
  /-- Letter formulas for the extra elements; sentences. -/
  labC : Fin extra → B → MSO A
  /-- Order formulas between two copies of positions; free variables `x₀, x₁`. -/
  ordPP : Fin copies → Fin copies → MSO A
  /-- Order formulas between a copy of a position and an extra element. -/
  ordPC : Fin copies → Fin extra → MSO A
  /-- Order formulas between an extra element and a copy of a position. -/
  ordCP : Fin extra → Fin copies → MSO A
  /-- Order formulas between two extra elements. -/
  ordCC : Fin extra → Fin extra → MSO A

namespace MSOTransduction

variable {A B : Type}

/-- The elements of the type `copies · n + extra`, before selection. -/
abbrev Elt (T : MSOTransduction A B) : Type := (Fin T.copies × ℕ) ⊕ Fin T.extra

/-- The elements selected by the universe formulas. -/
def selected (T : MSOTransduction A B) (w : List A) : T.Elt → Prop
  | Sum.inl (i, p) => p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (T.univP i)
  | Sum.inr j => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.univC j)

/-- The order defined by the order formulas. -/
def ordRel (T : MSOTransduction A B) (w : List A) : T.Elt → T.Elt → Prop
  | Sum.inl (i, p), Sum.inl (i', p') =>
      MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅) (T.ordPP i i')
  | Sum.inl (i, p), Sum.inr j => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordPC i j)
  | Sum.inr j, Sum.inl (i, p) => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordCP j i)
  | Sum.inr j, Sum.inr j' => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.ordCC j j')

/-- The labelling defined by the letter formulas. -/
def labRel (T : MSOTransduction A B) (w : List A) : T.Elt → B → Prop
  | Sum.inl (i, p), b => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.labP i b)
  | Sum.inr j, b => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.labC j b)

/-- The transduction outputs `v` on `w`: `v` lists the selected elements, without
repetition, in the order of the order formula, each labelled by a letter of
its letter formulas. -/
def Outputs (T : MSOTransduction A B) (w : List A) (v : List B) : Prop :=
  ∃ es : List T.Elt,
    es.Nodup ∧
    (∀ x, x ∈ es ↔ T.selected w x) ∧
    (∀ (i j : ℕ) (hi : i < es.length) (hj : j < es.length),
      i < j → T.ordRel w (es.get ⟨i, hi⟩) (es.get ⟨j, hj⟩)) ∧
    es.length = v.length ∧
    ∀ (i : ℕ) (hi : i < es.length) (hi' : i < v.length),
      T.labRel w (es.get ⟨i, hi⟩) (v.get ⟨i, hi'⟩)

/-- The requirement of Definition C.4.7: on every input, every selected element
satisfies exactly one letter formula, and the order formula is a linear order
on the selected elements. -/
def Proper (T : MSOTransduction A B) : Prop :=
  ∀ w : List A,
    (∀ x, T.selected w x → ∃! b, T.labRel w x b) ∧
    (∀ x, T.selected w x → T.ordRel w x x) ∧
    (∀ x y, T.selected w x → T.selected w y →
      T.ordRel w x y → T.ordRel w y x → x = y) ∧
    (∀ x y z, T.selected w x → T.selected w y → T.selected w z →
      T.ordRel w x y → T.ordRel w y z → T.ordRel w x z) ∧
    (∀ x y, T.selected w x → T.selected w y → T.ordRel w x y ∨ T.ordRel w y x)

/-- All formulas of the transduction are first-order. -/
def AllFO (T : MSOTransduction A B) : Prop :=
  (∀ i, (T.univP i).IsFO) ∧ (∀ j, (T.univC j).IsFO) ∧
  (∀ i b, (T.labP i b).IsFO) ∧ (∀ j b, (T.labC j b).IsFO) ∧
  (∀ i i', (T.ordPP i i').IsFO) ∧ (∀ i j, (T.ordPC i j).IsFO) ∧
  (∀ j i, (T.ordCP j i).IsFO) ∧ (∀ j j', (T.ordCC j j').IsFO)

end MSOTransduction

/-- A function defined by a string-to-string mso transduction satisfying the
requirements of the definition. -/
def IsMSOTransduction {A B : Type} (f : List A → List B) : Prop :=
  ∃ T : MSOTransduction A B, T.Proper ∧ ∀ w, T.Outputs w (f w)

/-- A function defined by a first-order transduction. -/
def IsFOTransduction {A B : Type} (f : List A → List B) : Prop :=
  ∃ T : MSOTransduction A B, T.Proper ∧ T.AllFO ∧ ∀ w, T.Outputs w (f w)

end Lax314295.MSOTransductions
