import Lax185574Proofs.ResolveRam.Glue.FilterCp
import Lax185574Proofs.ResolveRam.Glue.ReadX

/-!
The specifications of the pieces of the later rounds of the glue program
of lem:resolve-lift.

A piece is a command that appends a word to the buffer `OB` (with the
pointer `po`, as `Filled`). It reads the input `x` of the composite
(array `x`), the list of words of the word library (`WordsAt`, arrays
`a`, `st`, `ln`), the answer of the switch (array `y`) and scalars. The
names of the scalars it reads are fixed below. Every specification is a
statement about one command `cmd` and the list `tv` of the scalars that
it may write (`PFr`): it keeps all other scalars, the arrays `a`, `st`,
`ln`, `y`, `x`, the lengths of all arrays and the tapes. Before a piece
runs, all arrays have length `W + 1` (`ArrW`) and the word size leaves
room for the data (`Room W R S`: `2^16 (R+1)^2 (S+1)^2 ≤ W`, with `S` a
size of the input of the piece and `R` the largest radius it meets). The
cost bounds are linear in the size of the data that grows with `|G|`, and
polynomial in the size of the local data (one tree, its compositions, the
radius).

* `CTSpec`: the color table `ctW G P Q`, as a frame, from the input.
* `LV0Spec`: the item words of level `0`, as frames, from the input.
* `HSpec`: the word of the resolved graph and the word of its distance
  matrix, from the input.
* `FASpec`: the frames of the words of the answer of the far tree that
  pass `passSel` against the answer of the rank shift.
* `ExSpec`: the frames of the expansion words `exW` of an item, each
  with the index of the item in front.
* `AtSpec`: the word of the list of the new atom words of a tree (the
  query of the first canonical form of an item).
* `KidSpec`: the word of the list of the children words of an item (the
  query of the second canonical form of an item).

The pieces that write frames also leave the number of the frames in the
scalar `pc`.

The scalars read by the pieces: `W`; `nx` (`|x|`), `gn` (`n`), `gP`,
`gQ`, `gS` (`P`, `Q`, the sign as `0`/`1`); `oc` (index of the color
table in the library), `os` (index of the answer of the rank shift),
`ow` (index of an item word), `ii` (index of the item in its level),
`cl`, `cn` (first index and number of the compositions), `kl`, `kn`
(first index and number of the item words of the level below), `ol`
(first index of the output words of the level below, also `kn` of them),
`yo` (offset of the real answer in `y`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- The arrays that a piece keeps. -/
def keepA : List String := ["a", "st", "ln", "y", "x"]

/-- The frame of a piece that writes the scalars `tv`. -/
structure PFr (tv : List String) (τ τ' : Env) : Prop where
  vars : ∀ y, y ∉ tv → τ'.vars y = τ.vars y
  arrs : ∀ b ∈ keepA, τ'.arrs b = τ.arrs b
  len : ∀ b, (τ'.arrs b).length = (τ.arrs b).length
  out : τ'.out = τ.out
  inp : τ'.inp = τ.inp

/-- All arrays have length `W + 1`. -/
def ArrW (W : ℕ) (τ : Env) : Prop := ∀ b, (τ.arrs b).length = W + 1

/-- The word size leaves room for data of size `S` and radii up to `R`. -/
def Room (W R S : ℕ) : Prop := 2 ^ 16 * (R + 1) ^ 2 * (S + 1) ^ 2 ≤ W

/-- The longest word of a list. -/
def maxLen (L : List (List ℕ)) : ℕ := (L.map List.length).foldr max 0

/-- The array `y` holds the word `w` from the offset `yo`. -/
def YAt (w : List ℕ) (yo : ℕ) (τ : Env) : Prop := ∀ i (h : i < w.length), (τ.arrs "y")[yo + i]? = some w[i]

/-- The library word `ws[i]` is a color table with colors `cs`. -/
def IsCT (CT : List ℕ) : Prop := ∃ (cs : List ℕ) (f g : ℕ → ℕ), CT = cs.flatMap fun Y => [Y, f Y, g Y]

/-- The colors of a color table. -/
def ctCols : List ℕ → List ℕ
  | Y :: _ :: _ :: r => Y :: ctCols r
  | _ => []

theorem ctCols_flatMap (cs : List ℕ) (f g : ℕ → ℕ) :
    ctCols (cs.flatMap fun Y => [Y, f Y, g Y]) = cs := by
  induction cs with
  | nil => rfl
  | cons a l ih => simp [ctCols, ih]

theorem ctCols_ctW {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) : ctCols (ctW G P Q) = colsL G :=
  ctCols_flatMap _ _ _

theorem isCT_ctW {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) : IsCT (ctW G P Q) :=
  ⟨colsL G, _, _, rfl⟩

/-! ### The pieces that read the input -/

/-- **The color table.** -/
def CTSpec (cmd : Com) (tv : List String) : Prop :=
  ∃ cP : ℕ, ∀ (W k₀ q₀ : ℕ) {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (τ : Env)
    (pre : List ℕ),
    τ.vars "W" = W → ArrW W τ → PreAt "x" (xIn G k₀ q₀ P Q s) τ →
    τ.vars "nx" = (xIn G k₀ q₀ P Q s).length → τ.vars "gn" = n → τ.vars "gP" = P →
    τ.vars "gQ" = Q → Filled "OB" "po" pre τ →
    Room W 0 (ySz (xIn G k₀ q₀ P Q s) + pre.length) →
    ∃ τ', Run (W + 1) cmd τ τ' (cP * ((xIn G k₀ q₀ P Q s).length + 1)) ∧
      Filled "OB" "po" (pre ++ ((ctW G P Q).length :: ctW G P Q)) τ' ∧ PFr tv τ τ'

/-- **The item words of level `0`.** -/
def LV0Spec (cmd : Com) (tv : List String) : Prop :=
  ∃ cP : ℕ, ∀ (W k₀ q₀ : ℕ) {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (τ : Env)
    (pre : List ℕ),
    τ.vars "W" = W → ArrW W τ → PreAt "x" (xIn G k₀ q₀ P Q s) τ →
    τ.vars "nx" = (xIn G k₀ q₀ P Q s).length → τ.vars "gn" = n → Filled "OB" "po" pre τ →
    Room W 0 (ySz (xIn G k₀ q₀ P Q s) + pre.length) →
    ∃ τ', Run (W + 1) cmd τ τ' (cP * ((xIn G k₀ q₀ P Q s).length + 1)) ∧
      Filled "OB" "po" (pre ++ frames ((List.finRange n).map fun b =>
        itemW ((0, 0), family G k₀ q₀ b))) τ' ∧
      τ'.vars "pc" = n ∧ PFr tv τ τ'

/-- The word of the resolved graph followed by the word of its distance
matrix. -/
noncomputable def hWord {n : ℕ} (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) : List ℕ :=
  toWord (resolveBy G s P Q) ++ toWord (Lax185574.DistanceMatrix.distMatrix (resolveBy G s P Q))

/-- **The word of the resolved graph.** -/
def HSpec (cmd : Com) (tv : List String) : Prop :=
  ∃ cP : ℕ, ∀ (W k₀ q₀ : ℕ) {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (τ : Env)
    (pre : List ℕ),
    τ.vars "W" = W → ArrW W τ → PreAt "x" (xIn G k₀ q₀ P Q s) τ →
    τ.vars "nx" = (xIn G k₀ q₀ P Q s).length → τ.vars "gn" = n → τ.vars "gP" = P →
    τ.vars "gQ" = Q → τ.vars "gS" = (if s then 1 else 0) → Filled "OB" "po" pre τ →
    Room W 0 (ySz (xIn G k₀ q₀ P Q s) + pre.length) →
    ∃ τ', Run (W + 1) cmd τ τ' (cP * ((xIn G k₀ q₀ P Q s).length + 1)) ∧
      Filled "OB" "po" (pre ++ hWord G s P Q) τ' ∧ PFr tv τ τ'

/-! ### The pieces that read the word library -/

/-- **The filtered far tree.** The answer of the far tree, the word of
the list `L` of tree words, is in `y` from `yo`. -/
def FASpec (cmd : Com) (tv : List String) : Prop :=
  ∃ cP aP : ℕ, ∀ (W : ℕ) (τ : Env) (ws : List (List ℕ)) (L : List (List ℕ)) (pre : List ℕ)
    (oc os yo P Q sg : ℕ) (hoc : oc < ws.length) (hos : os < ws.length),
    τ.vars "W" = W → ArrW W τ → WordsAt ws τ → τ.vars "oc" = oc → τ.vars "os" = os →
    τ.vars "yo" = yo → τ.vars "gP" = P → τ.vars "gQ" = Q → P ≤ W → Q ≤ W → τ.vars "gS" = sg → sg ≤ 1 →
    IsCT ws[oc] → (∃ σ : TypeTree, ws[os] = toWord σ) → (∀ w ∈ L, ∃ ν : TypeTree, w = toWord ν) →
    YAt (toWord L) yo τ → Filled "OB" "po" pre τ →
    Room W (rhoPlus (ws[os].getD 0 0) (ws[os].getD 1 0))
      (ySz (toWord ws) + ySz (toWord L) + yo + pre.length + ws[os].getD 2 0) →
    ∃ τ', Run (W + 1) cmd τ τ' (cP * ((toWord L).length + ws[oc].length + 1) *
        (ws[os].length + ws[os].getD 2 0 + maxLen L + rhoPlus (ws[os].getD 0 0) (ws[os].getD 1 0) + 1) ^ aP) ∧
      Filled "OB" "po" (pre ++ frames (L.filter (passSel (dwOf P Q sg ws[oc]) ws[os]))) τ' ∧
      τ'.vars "pc" = (L.filter (passSel (dwOf P Q sg ws[oc]) ws[os])).length ∧ PFr tv τ τ'

/-- **The expansion of an item.** The item word is `ws[ow]`, the answers
of its compositions are the words `ws[cl], …, ws[cl + cn - 1]`, and `i`
is the index of the item in its level. -/
def ExSpec (cmd : Com) (tv : List String) : Prop :=
  ∃ cP aP : ℕ, ∀ (W : ℕ) (τ : Env) (ws : List (List ℕ)) (pre : List ℕ)
    (oc ow cl cn i P Q sg p g k q ℓ : ℕ) (t : Node (q + 1) ℓ) (hoc : oc < ws.length)
    (how : ow < ws.length),
    τ.vars "W" = W → ArrW W τ → WordsAt ws τ → τ.vars "oc" = oc → τ.vars "ow" = ow →
    τ.vars "cl" = cl → τ.vars "cn" = cn → cl + cn ≤ ws.length → τ.vars "ii" = i →
    τ.vars "gP" = P → τ.vars "gQ" = Q → P ≤ W → Q ≤ W → τ.vars "gS" = sg → sg ≤ 1 → IsCT ws[oc] →
    ws[ow] = itemW ((p, g), ⟨k, q + 1, ℓ, t⟩) →
    (∀ w ∈ (ws.drop cl).take cn, ∃ ν : TypeTree, w = toWord ν) → Filled "OB" "po" pre τ →
    Room W (rhoPlus (k + 1) q) (ySz (toWord ws) + i + pre.length + ℓ) →
    ∃ τ', Run (W + 1) cmd τ τ' (cP * (ws[oc].length + 1) *
        (ws[ow].length + ℓ + total ((ws.drop cl).take cn) + cn + rhoPlus (k + 1) q + 1) ^ aP) ∧
      Filled "OB" "po" (pre ++ frames ((exW (dwOf P Q sg ws[oc]) k q ℓ (toWord t)
        ((ws.drop cl).take cn)).map (i :: ·))) τ' ∧
      τ'.vars "pc" = (exW (dwOf P Q sg ws[oc]) k q ℓ (toWord t) ((ws.drop cl).take cn)).length ∧
      PFr tv τ τ'

/-- **The atom words of a tree.** The item word is `ws[ow]`. -/
def AtSpec (cmd : Com) (tv : List String) : Prop :=
  ∃ cP aP : ℕ, ∀ (W : ℕ) (τ : Env) (ws : List (List ℕ)) (pre : List ℕ)
    (oc ow P Q sg p g : ℕ) (σ : TypeTree) (hoc : oc < ws.length) (how : ow < ws.length),
    τ.vars "W" = W → ArrW W τ → WordsAt ws τ → τ.vars "oc" = oc → τ.vars "ow" = ow →
    τ.vars "gP" = P → τ.vars "gQ" = Q → P ≤ W → Q ≤ W → τ.vars "gS" = sg → sg ≤ 1 → IsCT ws[oc] →
    ws[ow] = itemW ((p, g), σ) → Filled "OB" "po" pre τ →
    Room W (rhoPlus σ.k σ.q) (ySz (toWord ws) + pre.length + σ.ℓ) →
    ∃ τ', Run (W + 1) cmd τ τ' (cP * (ws[oc].length + 1) *
        (ws[ow].length + σ.ℓ + rhoPlus σ.k σ.q + 1) ^ aP) ∧
      Filled "OB" "po" (pre ++ toWord ((candW σ.k σ.q σ.ℓ (ctCols ws[oc])).filter
        (newAtomW (dwOf P Q sg ws[oc]) (listWords (toWord σ) 3)))) τ' ∧ PFr tv τ τ'

/-- **The children words of an item.** The item word is `ws[ow]`, `i` its
index, the item words of the level below are `ws[kl], …, ws[kl + kn - 1]`
and their output words `ws[ol], …, ws[ol + kn - 1]`. -/
def KidSpec (cmd : Com) (tv : List String) : Prop :=
  ∃ cP aP : ℕ, ∀ (W : ℕ) (τ : Env) (ws : List (List ℕ)) (pre : List ℕ)
    (ow kl kn ol i p g k q ℓ : ℕ) (t : Node (q + 1) ℓ) (how : ow < ws.length),
    τ.vars "W" = W → ArrW W τ → WordsAt ws τ → τ.vars "ow" = ow → τ.vars "ii" = i →
    τ.vars "kl" = kl → τ.vars "kn" = kn → τ.vars "ol" = ol → kl + kn ≤ ws.length →
    ol + kn ≤ ws.length → ws[ow] = itemW ((p, g), ⟨k, q + 1, ℓ, t⟩) →
    Filled "OB" "po" pre τ → Room W 0 (ySz (toWord ws) + i + pre.length) →
    ∃ τ', Run (W + 1) cmd τ τ' (cP * (kn + total ((ws.drop kl).take kn) +
        total ((ws.drop ol).take kn) + 1) * (ws[ow].length + 1) ^ aP) ∧
      Filled "OB" "po" (pre ++ toWord (kidW q ℓ i
        (((ws.drop kl).take kn).map fun w => (w.getD 0 0, w.getD 1 0)) ((ws.drop ol).take kn))) τ' ∧
      PFr tv τ τ'

end Lax185574Proofs.ResolveRam.Glue
