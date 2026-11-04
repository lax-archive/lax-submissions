import Lax185574.ScatterTypes
import Lax185574.ConstructionSequences
import Lax185574Proofs.LegacyAttr

/-!
The names of the older word encoding, for the proofs written against it.

All encodings are given by the class `Lax185574.Encoding.Encode`. The
proofs of this package were written for an older class `WordEncoding`
with the function `toWord`, whose words are the same. Here `WordEncoding`
is an abbreviation of `Encode`, and `toWord` is notation for `encode`,
so every lemma about `toWord` is a lemma about `encode`.

The definitions of the older modules that now live elsewhere are made
available under their old names, as aliases (`export`) in the old
namespaces: `finsetOf`, `family`, `maxTreeSize`, `Step`, `Script`,
and `EncodesSequence` are the concept definitions themselves.
`EncodesInstance` is in `Lax185574Proofs.LegacyInstance`.

The older encoding functions of distance formulas, of first-order
formulas and of steps are kept as definitions by recursion, with the
equations `encode_eq_code`, `encode_eq_foCode` and `encode_eq_stepCode`.
The encoding of distance formulas and of first-order formulas is derived
by structural recursion, so it agrees with the older function only
propositionally.

The prefix property `PrefixFree` of an encoding, which makes it
injective, is stated here and proved in
`Lax185574Proofs.Words.PrefixFree` and
`Lax185574Proofs.EncodingInjectivity`.
-/

namespace Lax185574Proofs.Legacy

open Lax185574.Encoding Lax185574.Encodings Lax185574.ConstructionSequences
open Lax185574.DistanceLogic

universe u u'

/-- The older name of the class `Encode`. -/
abbrev WordEncoding (α : Type u) : Type u := Encode α

/-- The older name of `encode`, as notation, so that `toWord a` and
`encode a` are the same term. -/
notation (name := toWordNotation) "toWord" => Lax185574.Encoding.encode

/-- The encodings of the elements of a finite set, sorted
lexicographically. The encoding of the set is the encoding of this
list. -/
def Finset.words {α : Type u} [Encode α] (S : Finset α) : List (List ℕ) :=
  (S.image encode).sort (· ≤ ·)

/-- The encoding is a prefix code: a word starts with the encoding of at
most one element, so the encoding is injective and self-delimiting. -/
class PrefixFree (α : Type u) [Encode α] : Prop where
  /-- Two encodings that agree as the fronts of a word are equal, and so
  are the rests. -/
  prefix_inj : ∀ (a b : α) (r s : List ℕ), encode a ++ r = encode b ++ s → a = b ∧ r = s

/-- The three numbers encoding a step. -/
def stepCode : Step → List ℕ
  | .merge P Q => [0, P, Q]
  | .resolvePos P Q => [1, P, Q]
  | .resolveNeg P Q => [2, P, Q]

theorem encode_eq_stepCode (s : Step) : encode s = stepCode s := rfl

/-- The prefix encoding of a distance formula: an opcode followed by the
arguments, in the order of the constructor. -/
def DistFO.code : {ℓ : ℕ} → DistFO ℓ → List ℕ
  | _, .eq i j => [0, i, j]
  | _, .edge i j => [1, i, j]
  | _, .nonEdge i j => [2, i, j]
  | _, .color Y i => [3, Y, i]
  | _, .distLe r i j => [4, r, i, j]
  | _, .distColorLt r Y i => [5, r, Y, i]
  | _, .not φ => 6 :: DistFO.code φ
  | _, .and φ ψ => 7 :: (DistFO.code φ ++ DistFO.code ψ)
  | _, .exLocal i s φ => 8 :: i :: s :: DistFO.code φ

theorem encode_eq_code {ℓ : ℕ} (φ : DistFO ℓ) : encode φ = DistFO.code φ := by
  induction φ with
  | not φ ih => exact congrArg (6 :: ·) ih
  | and φ ψ ih ih' =>
    show [7] ++ encode φ ++ encode ψ = 7 :: (DistFO.code φ ++ DistFO.code ψ)
    rw [ih, ih']; rfl
  | exLocal i s φ ih =>
    show [8] ++ [i.val] ++ [s] ++ encode φ = 8 :: i.val :: s :: DistFO.code φ
    rw [ih]; rfl
  | _ => rfl

theorem encode_fun_eq_code {ℓ : ℕ} : (encode : DistFO ℓ → List ℕ) = DistFO.code :=
  funext encode_eq_code

/-- The prefix encoding of a first-order formula of `Lax3.FirstOrder`. -/
def FO.code : {k : ℕ} → Lax3.FirstOrder.FO k → List ℕ
  | _, .adj i j => [0, i, j]
  | _, .eq i j => [1, i, j]
  | _, .not φ => 2 :: FO.code φ
  | _, .and φ ψ => 3 :: (FO.code φ ++ FO.code ψ)
  | _, .ex φ => 4 :: FO.code φ

theorem encode_eq_foCode {k : ℕ} (φ : Lax3.FirstOrder.FO k) : encode φ = FO.code φ := by
  induction φ with
  | not φ ih => exact congrArg (2 :: ·) ih
  | and φ ψ ih ih' =>
    show [3] ++ encode φ ++ encode ψ = 3 :: (FO.code φ ++ FO.code ψ)
    rw [ih, ih']; rfl
  | ex φ ih => exact congrArg (4 :: ·) ih
  | _ => rfl

/-! The words of the basic types, as equations. Many encodings are
derived, and `simp [toWord]` unfolds them to their derived functions.
The simp set `word_simps` gives instead the words in the form of the
older instances, as pre-lemmas so that they apply first. -/

section Basic

variable {α : Type u} {β : Type u'} [Encode α] [Encode β]

@[word_simps ↓] theorem toWord_nat (n : ℕ) : toWord n = [n] := rfl
@[word_simps ↓] theorem toWord_fin {n : ℕ} (i : Fin n) : toWord i = [i.val] := rfl
@[word_simps ↓] theorem toWord_bool (b : Bool) : toWord b = [if b then 1 else 0] := by
  cases b <;> rfl
theorem toWord_true : toWord true = [1] := rfl
theorem toWord_false : toWord false = [0] := rfl
theorem toWord_pair (a : α) (b : β) : toWord (a, b) = toWord a ++ toWord b := rfl
@[word_simps ↓] theorem toWord_prod (p : α × β) : toWord p = toWord p.1 ++ toWord p.2 := rfl
@[word_simps ↓] theorem toWord_inl (a : α) : toWord (Sum.inl a : α ⊕ β) = 0 :: toWord a := rfl
@[word_simps ↓] theorem toWord_inr (b : β) : toWord (Sum.inr b : α ⊕ β) = 1 :: toWord b := rfl
@[word_simps ↓] theorem toWord_none : toWord (none : Option α) = [0] := rfl
@[word_simps ↓] theorem toWord_some (a : α) : toWord (some a) = 1 :: toWord a := rfl
@[word_simps ↓] theorem toWord_ofNat (m : ℕ) : toWord (Int.ofNat m) = [0, m] := rfl
@[word_simps ↓] theorem toWord_natCast (m : ℕ) : toWord (m : ℤ) = [0, m] := rfl
@[word_simps ↓] theorem toWord_negSucc (m : ℕ) : toWord (Int.negSucc m) = [1, m] := rfl
@[word_simps ↓] theorem toWord_rat (x : ℚ) : toWord x = toWord (x.num, x.den) := rfl
@[word_simps ↓] theorem toWord_list (l : List α) :
    toWord l = l.length :: (l.map toWord).flatten := rfl
@[word_simps ↓] theorem toWord_fun {n : ℕ} (f : Fin n → α) : toWord f = toWord (List.ofFn f) := rfl
@[word_simps ↓] theorem toWord_finset (S : Finset α) : toWord S = toWord (Finset.words S) := rfl
@[word_simps ↓] theorem toWord_enat (d : ℕ∞) : toWord d = [if d = ⊤ then 0 else d.toNat + 1] := rfl
@[word_simps ↓] theorem toWord_step (s : Step) : toWord s = stepCode s := rfl
@[word_simps ↓] theorem toWord_script {n : ℕ} (σ : Script n) :
    toWord σ = toWord (σ.colors, σ.steps) := rfl
@[word_simps ↓] theorem toWord_typeTree (τ : Lax185574.TypeTrees.TypeTree) :
    toWord τ = toWord (τ.k, τ.q, τ.ℓ) ++ toWord τ.root := rfl
@[word_simps ↓] theorem toWord_distFO {ℓ : ℕ} (φ : DistFO ℓ) : toWord φ = DistFO.code φ :=
  encode_eq_code φ
@[word_simps ↓] theorem toWord_fo {k : ℕ} (φ : Lax3.FirstOrder.FO k) : toWord φ = FO.code φ :=
  encode_eq_foCode φ

end Basic

end Lax185574Proofs.Legacy

/-! The old namespaces, with aliases of the names they provided. -/

set_option linter.dupNamespace false
namespace Lax185574.WordEncoding
export Lax185574Proofs.Legacy (WordEncoding Finset.words PrefixFree PrefixFree.prefix_inj)
export Lax185574.Encoding (wordLength)
export Lax185574.TypeTrees (finsetOf)
export Lax185574.ScatterTypes (graphOn)
end Lax185574.WordEncoding

namespace Lax185574.SequenceEncoding
export Lax185574.ConstructionSequences (Step Step.merge Step.resolvePos Step.resolveNeg apply
  unresolved Script Script.mk Script.colors Script.steps Script.run EncodesSequence)
export Lax185574Proofs.Legacy (stepCode)
end Lax185574.SequenceEncoding

namespace Lax185574.PartialGraphEncoding
export Lax185574.TypeTrees (family maxTreeSize)
end Lax185574.PartialGraphEncoding

namespace Lax185574.InstanceEncoding
export Lax185574Proofs.Legacy.FO (code)
end Lax185574.InstanceEncoding

namespace Lax185574.DistanceLogic.DistFO
export Lax185574Proofs.Legacy.DistFO (code)
end Lax185574.DistanceLogic.DistFO
