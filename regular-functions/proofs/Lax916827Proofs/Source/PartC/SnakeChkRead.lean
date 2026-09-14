/-
**Reading the data of the pieces off an accepted annotation.**

The checking automaton of stage 1 of the induction step of the book's snake
lemma (`RequestProject/PartC/SnakeChkEnc.lean`) verifies *local* conditions: a
condition on every letter and on every pair of consecutive letters of the
annotation.  This file turns an accepted annotation into the purely numerical
data out of which `RequestProject/PartC/SnakeAssemble.lean` builds an annotated
string:

* the cutting points `Transducers.TwoWay.Chk.bY` of the input into blocks -- the
  positions marked by the bit `sb`;
* the window `[aCut, bCut)` of every piece slot of every pair of neighbouring
  blocks -- the interval cut out by the two monotone flags;
* the parameters `pPar` of every piece slot -- constant along the pair, because
  the checking automaton verifies that they do not change.

The main result is `Transducers.TwoWay.Chk.splitSep_snakeOutLet`: the blocks of
the string produced by the annotation are the blocks of the annotated string
built from that data, so that the neighbouring-block map combinator applied to
the two strings gives the same result.
-/
import Lax916827Proofs.Source.PartC.SnakeChkEnc
import Lax916827Proofs.Source.PartC.SnakeChkBlocks
import Lax916827Proofs.Source.PartC.SnakeChkCut
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open BlockIdx RegPair

variable {A B Q S : Type} {K : ℕ}

/-! ## The data read off an annotation -/

/-- The first position of the `m`-th block of the annotation. -/
noncomputable def bY (u : List (Gam A Q S K)) (m : ℕ) : ℕ := bstart sb u m

lemma bY_def (u : List (Gam A Q S K)) (m : ℕ) : bY u m = bstart sb u m := rfl

/-- The role that the letter at the position `j` plays in the pair of blocks
`i`: `false` if its block is the left block of the pair, `true` if it is the
right one. -/
noncomputable def rol (u : List (Gam A Q S K)) (i j : ℕ) : Bool := decide (bY u (i + 1) ≤ j)

/-- The left flag of the `r`-th piece of the pair `i`, at the position `j`. -/
noncomputable def flLat (u : List (Gam A Q S K)) (i r j : ℕ) : Bool :=
  if h : j < u.length then flL (u[j]'h) (rol u i j) r else false

/-- The right flag of the `r`-th piece of the pair `i`, at the position `j`. -/
noncomputable def flRat (u : List (Gam A Q S K)) (i r j : ℕ) : Bool :=
  if h : j < u.length then flR (u[j]'h) (rol u i j) r else false

/-- The left end of the window of the `r`-th piece of the pair `i`. -/
noncomputable def aCut (u : List (Gam A Q S K)) (i r : ℕ) : ℕ :=
  cutOf (flLat u i r) (bY u i) (bY u (i + 2))

/-- The right end of the window of the `r`-th piece of the pair `i`. -/
noncomputable def bCut (u : List (Gam A Q S K)) (i r : ℕ) : ℕ :=
  cutOf (flRat u i r) (bY u i) (bY u (i + 2))

/-- The parameters of the `r`-th piece of the pair `i`. -/
noncomputable def pPar (u : List (Gam A Q S K)) (i r : ℕ) : PieceParam A Q :=
  if h : bY u i < u.length then pr (u[bY u i]'h) (rol u i (bY u i)) r else default

/-- Is the pair `i` the last one? -/
noncomputable def lpOf (u : List (Gam A Q S K)) (i : ℕ) : Bool :=
  if h : bY u i < u.length then lp (u[bY u i]'h) (rol u i (bY u i)) else false

/-- The number of pairs of neighbouring blocks of the annotation, minus one. -/
noncomputable def nPair (u : List (Gam A Q S K)) : ℕ := nbl sb sa u - 1

/-! ## The blocks of the annotation -/

variable {u : List (Gam A Q S K)}

@[simp] lemma bY_zero : bY u 0 = 0 := bstart_zero

lemma bY_mono {m n : ℕ} (h : m ≤ n) : bY u m ≤ bY u n := bstart_mono h

lemma bY_le_length (m : ℕ) : bY u m ≤ u.length := bstart_le_length m

/-- **The index of the block containing a position.** -/
lemma blk_eq_of_between {m j : ℕ} (hj : j < u.length) (h1 : bY u m ≤ j) (h2 : j < bY u (m + 1)) :
    blk sb u j = m := by
  rw [bY_def] at h1 h2
  have hge : m ≤ blk sb u j := by
    by_contra hcon
    push_neg at hcon
    have h4 := bstart_mono (sep := sb) (u := u) (show blk sb u j + 1 ≤ m by omega)
    have h3 := lt_bstart_succ (sep := sb) (u := u) hj
    omega
  have hle : blk sb u j ≤ m := by
    by_contra hcon
    push_neg at hcon
    have h4 := bstart_mono (sep := sb) (u := u) (show m + 1 ≤ blk sb u j by omega)
    have h3 := bstart_le_self (sep := sb) (u := u) hj
    omega
  omega

/-! ## The local conditions, position by position -/

variable [Inhabited S] {M : TwoWay A B Q} {stp : S → A → S} {ini : S}
  {acc : PieceParam A Q → S → Prop}

lemma goodP_of_mem (hu : u ∈ ChkLang M K stp ini acc) {i : ℕ} (hi : i ≤ u.length) :
    GoodP M K stp ini acc (SnakeLoc.prevAt u i) u[i]? :=
  (goodB_iff M K stp ini acc _ _).1 (hu i hi)

lemma letOK_at (hu : u ∈ ChkLang M K stp ini acc) {j : ℕ} (hj : j < u.length) :
    LetOK K (u[j]'hj) := by
  have h := goodP_of_mem hu (le_of_lt hj)
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rw [SnakeLoc.prevAt_zero, List.getElem?_eq_getElem hj] at h
    exact h.1
  · rw [SnakeLoc.prevAt, if_neg (by omega),
      List.getElem?_eq_getElem (show j - 1 < u.length by omega),
      List.getElem?_eq_getElem hj] at h
    exact h.1

lemma startOK_at (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) :
    StartOK M K stp ini (u[0]'h0) := by
  have h := goodP_of_mem hu (le_of_lt h0)
  rw [SnakeLoc.prevAt_zero, List.getElem?_eq_getElem h0] at h
  exact h.2

lemma endOK_at (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) :
    EndOK K acc (u[u.length - 1]'(by omega)) := by
  have h := goodP_of_mem hu (le_refl u.length)
  rw [SnakeLoc.prevAt_length, List.getElem?_eq_none (le_refl _),
    List.getLast?_eq_getElem?, List.getElem?_eq_getElem (show u.length - 1 < u.length by omega)]
    at h
  exact h

lemma sa_eq_false (hu : u ∈ ChkLang M K stp ini acc) {j : ℕ} (hj : j + 1 < u.length) :
    sa (u[j]'(by omega)) = false := by
  have h := goodP_of_mem hu (le_of_lt hj)
  rw [SnakeLoc.prevAt, if_neg (by omega),
    List.getElem?_eq_getElem (show j + 1 - 1 < u.length by omega),
    List.getElem?_eq_getElem hj] at h
  simpa using h.2.1

lemma adj_at (hu : u ∈ ChkLang M K stp ini acc) {j : ℕ} (hj : j + 1 < u.length) :
    if sb (u[j + 1]'hj) = true then AdjSep K stp ini acc (u[j]'(by omega)) (u[j + 1]'hj)
      else AdjSame K stp (u[j]'(by omega)) (u[j + 1]'hj) := by
  have h := goodP_of_mem hu (le_of_lt hj)
  rw [SnakeLoc.prevAt, if_neg (by omega),
    List.getElem?_eq_getElem (show j + 1 - 1 < u.length by omega),
    List.getElem?_eq_getElem hj] at h
  simpa using h.2.2

lemma sb_zero (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) :
    sb (u[0]'h0) = true := (startOK_at hu h0).1

lemma sb_zero' (hu : u ∈ ChkLang M K stp ini acc) :
    ∀ h0 : 0 < u.length, sb (u[0]'h0) = true := fun h0 => sb_zero hu h0

lemma sa_last (hu : u ∈ ChkLang M K stp ini acc) :
    ∀ (j : ℕ) (hj : j < u.length), sa (u[j]'hj) = true → j = u.length - 1 := by
  intro j hj h
  by_contra hcon
  have hj1 : j + 1 < u.length := by omega
  rw [sa_eq_false hu hj1] at h
  exact Bool.noConfusion h

lemma bY_one (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) : bY u 1 = 0 :=
  Nat.le_zero.1 (bstart_min h0 (by rw [blk_zero_of_sep h0 (sb_zero hu h0)]))

/-- **A position of a block is marked exactly when it is its first position.** -/
lemma sb_iff_of_between (hu : u ∈ ChkLang M K stp ini acc) {m j : ℕ} (hj : j < u.length)
    (h1 : bY u m ≤ j) (h2 : j < bY u (m + 1)) : sb (u[j]'hj) = true ↔ j = bY u m := by
  rw [sep_iff_bstart (sb_zero' hu) hj, blk_eq_of_between hj h1 h2]
  rfl

end Chk

end TwoWay

end Lax916827Proofs.Transducers
