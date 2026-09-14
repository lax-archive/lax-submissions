/-
The padded marked square of a string, and its index structure.

This file prepares the reduction of a `(k+1)`-pebble transducer to a `k`-pebble transducer used
in the proof of Theorem `thm:pebble-are-for` (the hard inclusion: a pebble transducer is simulated
by a for-transducer).  The reduction runs the simulating machine on the marked square of the
*padded* input

  `pad w = none :: w.map some ++ [none]`,

a string over `Option A` whose first and last letters are fresh.  The marked square of a string
`u` of length `N` is the concatenation of the `N` blocks

  `blk u i = (u.take (i+1)).map Sum.inl ++ (u.drop (i+1)).map Sum.inr`,

each of length `N`, so a gap of the marked square is a pair `(i, j)` of a block and an offset,
written `i * N + j`.  The padding makes every gap of `w` correspond to an offset `1 ≤ j ≤ N - 1`,
that is, to a gap strictly inside a block, which is what makes the block structure visible to the
simulating machine.

What is proved here: the padding is a rational (hence regular, hence polyregular) function, and
the letters of the marked square are given by `markedSquare_getElem?`.
-/
import Lax194892Proofs.Source.PartD.PolyDef
import Lax916827Proofs.Source.PartC.RatTools
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebSq

variable {A : Type}

/-! ## The padding -/

/-- The padded input: a fresh letter is added at both ends. -/
def pad (w : List A) : List (Option A) := none :: (w.map some ++ [none])

@[simp] lemma pad_length (w : List A) : (pad w).length = w.length + 2 := by
  simp [pad]

/-- The letter of the padded input at the index `i`, as an element of `Option A`. -/
def padLet (w : List A) (i : ℕ) : Option A := if i = 0 then none else w[i - 1]?

lemma pad_getElem? {w : List A} {i : ℕ} (hi : i < w.length + 2) :
    (pad w)[i]? = some (padLet w i) := by
  cases i with
  | zero => simp [pad, padLet]
  | succ i =>
      have h1 : (pad w)[i + 1]? = (w.map some ++ [none])[i]? := by
        simp [pad]
      rw [h1]
      by_cases hlt : i < w.length
      · rw [List.getElem?_append_left (by simpa using hlt)]
        simp [padLet, List.getElem?_map, List.getElem?_eq_getElem hlt]
      · have hi' : i = w.length := by simp at hi; omega
        subst hi'
        rw [List.getElem?_append_right (by simp)]
        simp [padLet]

/-- The padding is a rational function. -/
theorem isRationalFun_pad [Finite A] : IsRationalFun (pad : List A → List (Option A)) := by
  classical
  set ψ : Unit → Option A → Option A → List (Option A) := fun _ prev next =>
    (match prev with | none => [none] | some _ => []) ++
      (match next with | none => [none] | some a => [some a]) with hψ
  have htail : ∀ (w : List A) (x : A), ctxAux (ψ ()) (some x) w = w.map some ++ [none] := by
    intro w
    induction w with
    | nil => intro x; simp [hψ]
    | cons b w ih => intro x; simpa [hψ] using ih b
  have h : ∀ w : List A, ctxEval (fun (_ : Unit) (_ : A) => ()) () ψ w = pad w := by
    intro w
    rw [ctxEval]
    cases w with
    | nil => simp [hψ, pad]
    | cons a w =>
        rw [ctxAux_cons, htail w a]
        simp [hψ, pad]
  have hr := isRationalFun_ctxEval (fun (_ : Unit) (_ : A) => ()) () ψ
  have hfun : ctxEval (fun (_ : Unit) (_ : A) => ()) () ψ = pad := funext h
  rwa [hfun] at hr

/-- The padding is a regular function. -/
theorem isRegularFun_pad [Finite A] : IsRegularFun (pad : List A → List (Option A)) :=
  IsRegularFun.of_rational isRationalFun_pad

/-- The padding is a polyregular function. -/
theorem isPolyregular_pad [Finite A] : IsPolyregular (pad : List A → List (Option A)) :=
  IsPolyregular.of_regular isRegularFun_pad

/-! ## The index structure of the marked square -/

/-- The `i`-th block of the marked square of `u`. -/
def blk (u : List A) (i : ℕ) : List (A ⊕ A) :=
  (u.take (i + 1)).map Sum.inl ++ (u.drop (i + 1)).map Sum.inr

lemma blk_length {u : List A} {i : ℕ} (hi : i < u.length) : (blk u i).length = u.length := by
  simp [blk]
  omega

lemma markedSquare_eq_blocks (u : List A) :
    markedSquare A u = ((List.range u.length).map (blk u)).flatten := rfl

/-- Indexing the flattening of a list of lists that all have the same length. -/
lemma getElem?_flatten_const {α : Type} {N : ℕ} :
    ∀ (L : List (List α)), (∀ l ∈ L, l.length = N) → ∀ (i j : ℕ), j < N →
      L.flatten[i * N + j]? = (L[i]?).bind (fun l => l[j]?)
  | [], _, i, j, _ => by simp
  | l :: L, hL, i, j, hj => by
      have hl : l.length = N := hL l (by simp)
      cases i with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons]
          rw [List.getElem?_append_left (by omega)]
          simp
      | succ i =>
          have hidx : (i + 1) * N + j = l.length + (i * N + j) := by
            rw [hl]; ring
          simp only [List.flatten_cons, hidx]
          rw [List.getElem?_append_right (by omega)]
          simp only [Nat.add_sub_cancel_left]
          rw [getElem?_flatten_const L (fun l' hl' => hL l' (by simp [hl'])) i j hj]
          simp

/-- The letters of the marked square: in the block `i`, the letters up to the position `i` are
tagged `Sum.inl` and the later ones are tagged `Sum.inr`. -/
lemma markedSquare_getElem? {u : List A} {i j : ℕ} (hi : i < u.length) (hj : j < u.length) :
    (markedSquare A u)[i * u.length + j]? =
      some (if j ≤ i then Sum.inl u[j] else Sum.inr u[j]) := by
  rw [markedSquare_eq_blocks]
  rw [getElem?_flatten_const _ ?hlen i j hj]
  case hlen =>
    intro l hl
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨i', hi', rfl⟩ := hl
    exact blk_length hi'
  have hb : ((List.range u.length).map (blk u))[i]? = some (blk u i) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hi)]
    simp
  rw [hb, Option.bind_some]
  have hlen1 : ((u.take (i + 1)).map (Sum.inl : A → A ⊕ A)).length = min (i + 1) u.length := by
    simp
  by_cases hji : j ≤ i
  · rw [if_pos hji, blk, List.getElem?_append_left (by rw [hlen1]; omega),
      List.getElem?_map, List.getElem?_take, if_pos (by omega)]
    simp [List.getElem?_eq_getElem hj]
  · rw [if_neg hji, blk, List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
      show min (i + 1) u.length = i + 1 by omega, List.getElem?_map, List.getElem?_drop,
      show i + 1 + (j - (i + 1)) = j by omega]
    simp [List.getElem?_eq_getElem hj]

@[simp] lemma markedSquare_length (u : List A) :
    (markedSquare A u).length = u.length * u.length := by
  rw [markedSquare_eq_blocks, List.length_flatten]
  have h : ((List.range u.length).map (blk u)).map List.length
      = (List.range u.length).map (fun _ => u.length) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro i hi
    exact blk_length (by simpa using hi)
  rw [h]
  simp

end PebSq

end Lax194892Proofs.Transducers
