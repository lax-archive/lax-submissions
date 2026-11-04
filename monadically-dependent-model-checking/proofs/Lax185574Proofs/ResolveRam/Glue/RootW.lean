import Lax185574Proofs.ResolveRam.FarFilter
import Lax185574Proofs.ResolveRam.AtomList
import Lax185574Proofs.EvalRam.Word

/-!
The tests of lem:resolve-lift on the words of a root.

The glue program reads the atoms of a root as the list of their words
(`(Node.atoms t).words`). `DW` holds the data of the resolve that the
tests need: the colors `P`, `Q`, the sign, whether `P` and `Q` occur, and
the tables `cTab G P ·` and `cTab G Q ·` of the distances from the two
classes. On these, `nearW`, `hopW`, `hop2W`, `uHopW` and `newAtomW` are the
tests `nearA`, `hopTest`, `hop2`, `unaryHopTest` and `newAtomTest`
(`hopW_eq`, `hop2W_eq`, `uHopW_eq`, `newAtomW_eq`), if the data agree
with those of the resolve (`DW.OK`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.ResolveRam
open Lax185574Proofs.EvalRam

/-- The data of the resolve, as the tests use them. -/
structure DW where
  /-- The first color. -/
  P : ℕ
  /-- The second color. -/
  Q : ℕ
  /-- The sign. -/
  sg : Bool
  /-- `P` occurs. -/
  cP : Bool
  /-- `Q` occurs. -/
  cQ : Bool
  /-- One more than the distance from the class `P`, `0` if none. -/
  tP : ℕ → ℕ
  /-- One more than the distance from the class `Q`, `0` if none. -/
  tQ : ℕ → ℕ

/-- The table `t` gives `cd X · r` (an entry `t Y ≠ 0` with `t Y ≤ r + 1`). -/
def tabT (t : ℕ → ℕ) (Y r : ℕ) : Bool := t Y != 0 && decide (t Y ≤ r + 1)

/-- The data agree with those of the resolve. -/
structure DW.OK (Dw : DW) (D : ResolveData) : Prop where
  P : Dw.P = D.P
  Q : Dw.Q = D.Q
  sg : Dw.sg = D.sign
  cP : Dw.cP = decide (D.P ∈ D.cols)
  cQ : Dw.cQ = decide (D.Q ∈ D.cols)
  tP : ∀ Y r, D.cd D.P Y r = tabT Dw.tP Y r
  tQ : ∀ Y r, D.cd D.Q Y r = tabT Dw.tQ Y r

/-- Membership of a word in a list of words. -/
def inW (A : List (List ℕ)) (w : List ℕ) : Bool := decide (w ∈ A)

theorem inW_atoms {q ℓ : ℕ} (t : Node q ℓ) (φ : DistFO ℓ) :
    inW (Node.atoms t).words (code φ) = decide (inA t φ) := by
  rw [inW, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact code_mem_words

/-- The test `dist(xᵢ, X) < s + 1` on the atom words. -/
def nearW (A : List (List ℕ)) (X s i : ℕ) : Bool := inW A [5, s + 1, X, i]

theorem nearW_eq {q ℓ : ℕ} (t : Node q ℓ) (X s : ℕ) (i : Fin ℓ) :
    nearW (Node.atoms t).words X s i = decide (nearA t X s i) := by
  rw [nearW, show decide (nearA t X s i) = decide (inA t (.distColorLt (s + 1) X i)) from rfl,
    ← inW_atoms]
  rfl

/-- The test of `Hop` between position `i` of `A₁` and position `j` of `A₂`. -/
def hop2W (Dw : DW) (A₁ : List (List ℕ)) (i : ℕ) (A₂ : List (List ℕ)) (j s : ℕ) : Bool :=
  (List.range (s + 1)).any fun s₁ => (List.range (s + 1)).any fun s₂ =>
    (decide (s₁ + 1 + s₂ ≤ s) && ((nearW A₁ Dw.P s₁ i && nearW A₂ Dw.Q s₂ j) ||
      (nearW A₁ Dw.Q s₁ i && nearW A₂ Dw.P s₂ j))) ||
    (decide (s₁ + 2 + s₂ ≤ s) && ((nearW A₁ Dw.P s₁ i && nearW A₂ Dw.P s₂ j && Dw.cQ) ||
      (nearW A₁ Dw.Q s₁ i && nearW A₂ Dw.Q s₂ j && Dw.cP)))

/-- The test of `Hop` between positions `i` and `j` of one root. -/
def hopW (Dw : DW) (A : List (List ℕ)) (s i j : ℕ) : Bool := hop2W Dw A i A j s

theorem any_range_iff (N : ℕ) (f : ℕ → Bool) :
    (List.range N).any f = true ↔ ∃ s ∈ Finset.range N, f s = true := by
  simp [List.any_eq_true]

theorem hop2W_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) {q₁ ℓ₁ q₂ ℓ₂ : ℕ} (t₁ : Node q₁ ℓ₁)
    (i : Fin ℓ₁) (t₂ : Node q₂ ℓ₂) (j : Fin ℓ₂) (s : ℕ) :
    hop2W Dw (Node.atoms t₁).words i (Node.atoms t₂).words j s = decide (hop2 D t₁ i t₂ j s) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold hop2W hop2
  simp only [any_range_iff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, nearW_eq, h.P,
    h.Q, h.cP, h.cQ, and_assoc]

theorem hopW_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) {q ℓ : ℕ} (t : Node q ℓ) (s : ℕ)
    (i j : Fin ℓ) : hopW Dw (Node.atoms t).words s i j = decide (hopTest D t s i j) := by
  rw [hopW, hop2W_eq h, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  rfl

/-- The test of `Hop` from position `i` to the class `Y`. -/
def uHopW (Dw : DW) (A : List (List ℕ)) (s Y i : ℕ) : Bool :=
  (List.range (s + 1)).any fun s₁ => (List.range (s + 1)).any fun s₂ =>
    (decide (s₁ + 1 + s₂ ≤ s) && ((nearW A Dw.P s₁ i && tabT Dw.tQ Y s₂) ||
      (nearW A Dw.Q s₁ i && tabT Dw.tP Y s₂))) ||
    (decide (s₁ + 2 + s₂ ≤ s) && ((nearW A Dw.P s₁ i && tabT Dw.tP Y s₂ && Dw.cQ) ||
      (nearW A Dw.Q s₁ i && tabT Dw.tQ Y s₂ && Dw.cP)))

theorem uHopW_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) {q ℓ : ℕ} (t : Node q ℓ) (s Y : ℕ)
    (i : Fin ℓ) : uHopW Dw (Node.atoms t).words s Y i = decide (unaryHopTest D t s Y i) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold uHopW unaryHopTest
  simp only [any_range_iff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, nearW_eq, h.P,
    h.Q, h.cP, h.cQ, ← h.tP, ← h.tQ, and_assoc]

/-- The positions `i` and `j` carry the colors `P` and `Q`. -/
def crossW (Dw : DW) (A : List (List ℕ)) (i j : ℕ) : Bool :=
  (inW A [3, Dw.P, i] && inW A [3, Dw.Q, j]) || (inW A [3, Dw.Q, i] && inW A [3, Dw.P, j])

/-- The test whether an atom, given by its word, holds after the resolve. -/
def newAtomW (Dw : DW) (A : List (List ℕ)) : List ℕ → Bool
  | [0, i, j] => inW A [0, i, j]
  | [1, i, j] => inW A [1, i, j] ||
      (Dw.sg && crossW Dw A i j && !inW A [0, i, j] && !inW A [2, i, j])
  | [2, i, j] => inW A [2, i, j] ||
      (!Dw.sg && crossW Dw A i j && !inW A [0, i, j] && !inW A [1, i, j])
  | [3, Y, i] => inW A [3, Y, i]
  | [4, s, i, j] => inW A [4, s, i, j] || hopW Dw A s i j
  | [5, s, Y, i] => inW A [5, s, Y, i] || (decide (1 ≤ s) && uHopW Dw A (s - 1) Y i)
  | _ => false

theorem crossW_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) {q ℓ : ℕ} (t : Node q ℓ) (i j : Fin ℓ) :
    crossW Dw (Node.atoms t).words i j = decide (crossA D t i j) := by
  have e : ∀ (Y : ℕ) (k : Fin ℓ), inW (Node.atoms t).words [3, Y, k] = decide (inA t (.color Y k)) :=
    fun Y k => inW_atoms t (.color Y k)
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold crossW crossA
  simp only [e, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, h.P, h.Q]

/-- **The test of a new atom on the atom words.** -/
theorem newAtomW_iff {Dw : DW} {D : ResolveData} (h : Dw.OK D) {q ℓ : ℕ} (t : Node q ℓ)
    (φ : DistFO ℓ) : newAtomW Dw (Node.atoms t).words (code φ) = true ↔ newAtomTest D t φ := by
  have e : ∀ ψ : DistFO ℓ, inW (Node.atoms t).words (code ψ) = true ↔ inA t ψ := fun ψ => by
    rw [inW_atoms, decide_eq_true_iff]
  have hc : ∀ i j : Fin ℓ, crossW Dw (Node.atoms t).words i j = true ↔ crossA D t i j :=
    fun i j => by rw [crossW_eq h, decide_eq_true_iff]
  have hh : ∀ (s : ℕ) (i j : Fin ℓ), hopW Dw (Node.atoms t).words s i j = true ↔ hopTest D t s i j :=
    fun s i j => by rw [hopW_eq h, decide_eq_true_iff]
  have hu : ∀ (s Y : ℕ) (i : Fin ℓ), uHopW Dw (Node.atoms t).words s Y i = true ↔
      unaryHopTest D t s Y i := fun s Y i => by rw [uHopW_eq h, decide_eq_true_iff]
  cases φ with
  | eq i j => exact e (.eq i j)
  | edge i j =>
    have h1 := e (.edge i j); have h0 := e (.eq i j); have h2 := e (.nonEdge i j)
    simp only [code] at h1 h0 h2
    simp only [code, newAtomW, newAtomTest, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      h1, ← Bool.not_eq_true, h0, h2, hc, h.sg, and_assoc]
  | nonEdge i j =>
    have h1 := e (.edge i j); have h0 := e (.eq i j); have h2 := e (.nonEdge i j)
    simp only [code] at h1 h0 h2
    simp only [code, newAtomW, newAtomTest, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      h2, ← Bool.not_eq_true, h0, h1, hc, h.sg, and_assoc]
  | color Y i => exact e (.color Y i)
  | distLe s i j =>
    have h1 := e (.distLe s i j)
    simp only [code] at h1
    simp only [code, newAtomW, newAtomTest, Bool.or_eq_true, h1, hh]
  | distColorLt s Y i =>
    have h1 := e (.distColorLt s Y i)
    simp only [code] at h1
    simp only [code, newAtomW, newAtomTest, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      h1, hu, Finset.mem_range]
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨s - 1, by omega, by omega, h2⟩
    · rintro (h1 | ⟨s', h1, rfl, h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, by simpa using h2⟩
  | not φ => simp [code, newAtomW, newAtomTest]
  | and φ ψ => simp [code, newAtomW, newAtomTest]
  | exLocal i s φ => simp [code, newAtomW, newAtomTest]

/-- The words of the candidate atoms, in the order of the program. -/
def candW (k q ℓ : ℕ) (cs : List ℕ) : List (List ℕ) := (candL k q ℓ cs).map code

/-- **The words of the new atoms.** -/
theorem atomL_words {Dw : DW} {D : ResolveData} (h : Dw.OK D) (k q : ℕ) (cs : List ℕ) {q' ℓ : ℕ}
    (t : Node q' ℓ) :
    (atomL D k q cs t).map toWord = (candW k q ℓ cs).filter (newAtomW Dw (Node.atoms t).words) := by
  unfold atomL candW
  rw [Lax185574Proofs.Legacy.encode_fun_eq_code, List.filter_map]
  congr 1
  apply List.filter_congr
  intro φ _
  show decide (newAtomTest D t φ) = newAtomW Dw (Node.atoms t).words (code φ)
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact (newAtomW_iff h t φ).symm

end Lax185574Proofs.ResolveRam.Glue
