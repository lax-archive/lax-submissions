/-
Basic notions shared by all parts of the book
  *Transducers* (M. Bojańczyk, June 25, 2026).

Strings over an alphabet `A` are modelled as `List A`, and languages as
`Language A = Set (List A)`.  Regularity of a language is Mathlib's
`Language.IsRegular`.

Alphabets are assumed to be finite whenever the book assumes so; this is
recorded by `[Finite A]` instance arguments.
-/
import Mathlib

namespace Lax765601Proofs.Transducers

/-! ## Continuity (Definition `def:continuity`) -/

/-- **Definition `def:continuity` (Continuous string-to-string functions).**
A function `f : A* → B*` is continuous if the inverse image of every regular
language over the output alphabet is regular. -/
def Continuous {A B : Type} (f : List A → List B) : Prop :=
  ∀ L : Language B, L.IsRegular → Language.IsRegular ({w : List A | f w ∈ L} : Language A)

/-- Continuity for *partial* string-to-string functions, modelled as functions
into `Option (List B)`; the inverse image of `L` consists of those inputs whose
output is defined and belongs to `L`. -/
def PartialContinuous {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∀ L : Language B, L.IsRegular →
    Language.IsRegular ({w : List A | ∃ v, f w = some v ∧ v ∈ L} : Language A)

/-- Continuity for relations: the inverse image of a regular language under a
relation `R ⊆ A* × B*`. -/
def RelContinuous {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∀ L : Language B, L.IsRegular →
    Language.IsRegular ({w : List A | ∃ v, R w v ∧ v ∈ L} : Language A)

/-! ## Elementary properties of string-to-string functions -/

/-- `f` is prefix preserving: `w ⊑ v` implies `f w ⊑ f v`. -/
def PrefixPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w v : List A, w <+: v → f w <+: f v

/-- `f` is length preserving (equivalently, letter-to-letter). -/
def LengthPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w : List A, (f w).length = w.length

/-- The `n`-fold concatenation `v^n` of a string with itself. -/
def npow {A : Type} (v : List A) : ℕ → List A
  | 0 => []
  | n + 1 => v ++ npow v n

@[simp] lemma npow_zero {A : Type} (v : List A) : npow v 0 = [] := rfl

lemma npow_succ {A : Type} (v : List A) (n : ℕ) : npow v (n + 1) = v ++ npow v n := rfl

lemma npow_add {A : Type} (v : List A) (m n : ℕ) :
    npow v (m + n) = npow v m ++ npow v n := by
  induction m with
  | zero => simp [npow_zero]
  | succ m ih =>
    conv_lhs => rw [show m + 1 + n = (m + n) + 1 by omega]
    simp [npow_succ, ih, List.append_assoc]

lemma npow_succ' {A : Type} (v : List A) (n : ℕ) : npow v (n + 1) = npow v n ++ v := by
  rw [npow_add]
  simp [npow_succ]

@[simp] lemma npow_length {A : Type} (v : List A) (n : ℕ) :
    (npow v n).length = n * v.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [npow_succ, ih]; ring

@[simp] lemma npow_nil {A : Type} (n : ℕ) : npow ([] : List A) n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [npow_succ, ih]

/-- **Definition `def:aperiodic-mealy` (Aperiodic).**  A string-to-string function is aperiodic
if for all input strings `u, v, w` the last letter of `f (u vⁿ w)` is the same
for all sufficiently large `n`.

The last letter is taken as an element of `Option B`, i.e. the condition is that
the sequence `n ↦ (f (u vⁿ w)).getLast?` is eventually constant.  This is the
faithful reading of the book's definition: demanding an actual output *letter*
`b : B` would make the notion unsatisfiable for every letter-to-letter function,
since for `u = v = w = ε` the output `f ε` is empty and has no last letter.

The previous, degenerate version of this definition was
```
∀ u v w : List A, ∃ b : B, ∃ N : ℕ, ∀ n ≥ N,
  (f (u ++ npow v n ++ w)).getLast? = some b
```
which is never satisfied by a function computed by a Mealy machine. -/
def Aperiodic {A B : Type} (f : List A → List B) : Prop :=
  ∀ u v w : List A, ∃ o : Option B, ∃ N : ℕ, ∀ n ≥ N,
    (f (u ++ npow v n ++ w)).getLast? = o

/-! ## The map lifting (Definition `def:map-lifting`) -/

/-- Split a string over the alphabet `A + 1` (where `none` is the separator `#`)
into the list of maximal blocks that do not use the separator. -/
def splitSep {A : Type} : List (Option A) → List (List A)
  | [] => [[]]
  | none :: w => [] :: splitSep w
  | some a :: w =>
      match splitSep w with
      | [] => [[a]]
      | u :: us => (a :: u) :: us

/-- **Definition `def:map-lifting` (Map lifting).**  `mapLift f` applies `f` to every block
of the input string that is delimited by the fresh separator `#` (modelled by
`none`):  `w₁ # ⋯ # wₙ ↦ f w₁ # ⋯ # f wₙ`. -/
def mapLift {A B : Type} (f : List A → List B) (w : List (Option A)) :
    List (Option B) :=
  List.intercalate [none] ((splitSep w).map (fun u => (f u).map some))

/-! ## Left distance (Definition `def:left-distance`) -/

/-- **Definition `def:left-distance` (Left distance).**  The left distance `‖w₁, w₂‖` is the
least `k` such that `w₁ = v v₁` and `w₂ = v v₂` with `|v₁|, |v₂| ≤ k`. -/
noncomputable def leftDist {B : Type} (w₁ w₂ : List B) : ℕ :=
  sInf {k : ℕ | ∃ v v₁ v₂ : List B,
    w₁ = v ++ v₁ ∧ w₂ = v ++ v₂ ∧ v₁.length ≤ k ∧ v₂.length ≤ k}

/-! ## Deterministic transition functions -/

/-- The state transformation of a string, for a deterministic transition
function `δ : Q × A → Q`. -/
def strTrans {A Q : Type} (δ : Q → A → Q) (w : List A) : Q → Q := fun q => w.foldl δ q

/-- A deterministic transition function is *aperiodic* if for every state transformation `δ_w`
arising from an input string, the sequence `δ_w¹, δ_w², …` eventually stabilises (condition (*) of
Lemma `lem:aperiodicity-minimal-machine`). -/
def TransAperiodic {A Q : Type} (δ : Q → A → Q) : Prop :=
  ∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, (strTrans δ w)^[n] = (strTrans δ w)^[N]

/-! ## Closure under composition -/

/-- The closure of a family `P` of string-to-string functions (indexed by the
input and output alphabets) under composition.  This is the "Kleene star"
`P*` used throughout the book to describe classes of functions defined as
finite compositions of prime functions.  Intermediate alphabets are required to
be finite. -/
inductive CompClosure (P : ∀ (A B : Type), (List A → List B) → Prop) :
    ∀ (A B : Type), (List A → List B) → Prop
  | base {A B : Type} {f : List A → List B} : P A B f → CompClosure P A B f
  | protected id (A : Type) : CompClosure P A A _root_.id
  | comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C} :
      CompClosure P A B f → CompClosure P B C g → CompClosure P A C (g ∘ f)

/-- The union of two families of functions. -/
def FamUnion (P Q : ∀ (A B : Type), (List A → List B) → Prop) :
    ∀ (A B : Type), (List A → List B) → Prop :=
  fun A B f => P A B f ∨ Q A B f

end Lax765601Proofs.Transducers