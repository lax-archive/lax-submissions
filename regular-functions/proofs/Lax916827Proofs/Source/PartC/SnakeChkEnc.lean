/-
**The annotated alphabet of stage 1 of the induction step of the book's snake
lemma, and the language of the checking automaton.**

The book's first stage guesses the record-breaking columns and the pieces of the
record-breaker decomposition and *checks* the guess.  The guess is an annotation
of the input, letter by letter; this file fixes the annotation alphabet
(`Transducers.TwoWay.Chk.Gam`), the two homomorphisms through which Nivat's
construction reads and writes it (`Transducers.TwoWay.Chk.snakeIn` and
`Transducers.TwoWay.Chk.snakeOutLet`), and the *checking condition*, which is a
condition on pairs of consecutive annotated letters
(`Transducers.TwoWay.Chk.GoodP`), hence defines a regular language
(`Transducers.TwoWay.Chk.isRegular_chkLang`).

Every annotated letter carries

* the letter of the input itself;
* the bit `sb` saying that a block boundary precedes it and the bit `sa` saying
  that a block boundary follows it -- the latter is used only at the last letter
  of the input, so that the last block may be empty;
* for each of the two *roles* -- `false`: the letter's block is the left block of
  the pair of neighbouring blocks in question, `true`: it is the right one --
  and for each of the `2K+1` piece slots of a pair:
  * the two monotone flags `flL`, `flR` marking the left and the right end of
    the window of that piece,
  * the parameters `pr` of the window transducer of that piece,
  * the state `ds` of a deterministic automaton for the window conditions
    (`Transducers.TwoWay.Chk.WinCond`), accumulated over the window letters of
    that piece read so far;
* for each role, the bit `lp` saying that the pair in question is the last one.

The flags are checked to be monotone along the pair, so that they mark an
interval -- the window -- and the whole annotation is checked to describe a
*chain of pieces*: the first piece starts at the left end of the input in the
initial state, consecutive pieces meet at a common cut in a common state, and
the last piece of the last pair halts.  This is what
`RequestProject/PartC/SnakeChkGeom.lean` reads off the checking condition
(`Transducers.TwoWay.Chk.chk_sound`).
-/
import Lax916827Proofs.Source.PartC.SnakeChkWin
import Lax916827Proofs.Source.PartC.SnakeLocLang
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open SnakeLoc

variable {A B Q S : Type}

/-! ## The annotated alphabet -/

/-- The datum that the annotation of stage 1 attaches to a letter: the two block
boundary bits, the "last pair" bit of each role, the two flags, the parameters
and the automaton state of each role and each piece slot. -/
abbrev Dat (A Q S : Type) (K : ℕ) : Type :=
  Bool × Bool × (Bool → Bool)
    × (Bool → Fin (2 * K + 1) → Bool) × (Bool → Fin (2 * K + 1) → Bool)
    × (Bool → Fin (2 * K + 1) → PieceParam A Q) × (Bool → Fin (2 * K + 1) → S)

/-- An annotated letter. -/
abbrev Gam (A Q S : Type) (K : ℕ) : Type := A × Dat A Q S K

variable {K : ℕ}

/-- The letter of the input carried by an annotated letter. -/
def lt (c : Gam A Q S K) : A := c.1

/-- Does a block boundary precede the letter? -/
def sb (c : Gam A Q S K) : Bool := c.2.1

/-- Does a block boundary follow the letter?  Only the last letter of the input
may use this bit. -/
def sa (c : Gam A Q S K) : Bool := c.2.2.1

/-- Is the pair of blocks of the given role the last one? -/
def lp (c : Gam A Q S K) (s : Bool) : Bool := c.2.2.2.1 s

/-- The flag marking the left end of the window of the `r`-th piece. -/
def flL (c : Gam A Q S K) (s : Bool) (r : ℕ) : Bool :=
  if h : r < 2 * K + 1 then c.2.2.2.2.1 s ⟨r, h⟩ else false

/-- The flag marking the right end of the window of the `r`-th piece. -/
def flR (c : Gam A Q S K) (s : Bool) (r : ℕ) : Bool :=
  if h : r < 2 * K + 1 then c.2.2.2.2.2.1 s ⟨r, h⟩ else false

/-- The parameters of the `r`-th piece of the pair of the given role. -/
def pr (c : Gam A Q S K) (s : Bool) (r : ℕ) : PieceParam A Q :=
  if h : r < 2 * K + 1 then c.2.2.2.2.2.2.1 s ⟨r, h⟩ else default

/-- The automaton state of the `r`-th piece of the pair of the given role. -/
def ds [Inhabited S] (c : Gam A Q S K) (s : Bool) (r : ℕ) : S :=
  if h : r < 2 * K + 1 then c.2.2.2.2.2.2.2 s ⟨r, h⟩ else default

/-- Does the letter belong to the window of the `r`-th piece of the pair of the
given role? -/
def wb (c : Gam A Q S K) (s : Bool) (r : ℕ) : Bool := flL c s r && !flR c s r

/-- The kind of the `r`-th piece of the pair of the given role. -/
def kd (c : Gam A Q S K) (s : Bool) (r : ℕ) : Fin 5 := (pr c s r).1

/-- The flag whose transition marks the cut at which the `r`-th piece *starts*:
the left end of its window for the kinds `1` and `3`, the right end for the
kinds `2` and `4`. -/
def startfl (c : Gam A Q S K) (s : Bool) (r : ℕ) : Bool :=
  if kd c s r = 1 ∨ kd c s r = 3 then flL c s r else flR c s r

/-- The flag whose transition marks the cut at which the `r`-th piece *ends*.
It is used only for the kinds `1` and `2`, the pieces of the kinds `3` and `4`
halting inside their window. -/
def endfl (c : Gam A Q S K) (s : Bool) (r : ℕ) : Bool :=
  if kd c s r = 1 then flR c s r else flL c s r

/-- The slot data that the annotated letter contributes to the marked input:
the even slots carry the data of the role `false`, the odd ones that of the role
`true` (`TwoWay.slot`). -/
def slotsOf (c : Gam A Q S K) : Fin (2 * (2 * K + 1)) → Bool × PieceParam A Q :=
  fun t => (wb c (decide (t.val % 2 = 1)) (t.val / 2),
    pr c (decide (t.val % 2 = 1)) (t.val / 2))

/-- Erasing the annotation. -/
def snakeIn (K : ℕ) : Gam A Q S K → List A := fun c => [lt c]

/-- Inserting the block separators and keeping the slot data. -/
def snakeOutLet (K : ℕ) :
    Gam A Q S K → List (Option (SnakeLet A Q (2 * (2 * K + 1)))) :=
  fun c => (if sb c then [none] else []) ++ some (lt c, slotsOf c) ::
    (if sa c then [none] else [])

lemma homOf_snakeIn (u : List (Gam A Q S K)) : homOf (snakeIn K) u = u.map lt := by
  induction u with
  | nil => rfl
  | cons c u ih =>
      rw [homOf, List.map_cons, List.flatten_cons, ← homOf, ih, snakeIn,
        List.singleton_append, List.map_cons]

/-! ## The checking condition -/

section Cond

/-- The conditions on a single annotated letter: the window of every piece is an
interval, the kinds follow the pattern of the record-breaker decomposition, the
pieces of a pair meet at a common cut in a common state, the first piece of a
pair starts at the boundary between its two blocks and the last one ends at the
right end of the pair, and the last piece of a pair links to the first piece of
the next pair. -/
def LetOK (K : ℕ) (c : Gam A Q S K) : Prop :=
  (∀ s r, flR c s r = true → flL c s r = true)
  ∧ (∀ s r, r + 1 < 2 * K + 1 → kd c s r = 1 ∨ kd c s r = 2)
  ∧ (∀ s, lp c s = false → kd c s (2 * K) = 1 ∨ kd c s (2 * K) = 2)
  ∧ (∀ s, lp c s = true → kd c s (2 * K) = 3 ∨ kd c s (2 * K) = 4)
  ∧ (∀ s r, r < 2 * K + 1 → ∃ q f, stOf (pr c s r) = some (q, f))
  ∧ (∀ s, lp c s = true → entOf (pr c s (2 * K)) = extOf (pr c s (2 * K)))
  ∧ (∀ s r, r + 1 < 2 * K + 1 → extOf (pr c s r) = entOf (pr c s (r + 1)))
  ∧ (∀ s r, r + 1 < 2 * K + 1 → endfl c s r = startfl c s (r + 1))
  ∧ startfl c false 0 = false
  ∧ startfl c true 0 = true
  ∧ (∀ s, lp c s = false → endfl c s (2 * K) = false)
  ∧ (lp c true = false → extOf (pr c true (2 * K)) = entOf (pr c false 0))
  ∧ (lp c true = true → lp c false = false)

/-- The conditions on two consecutive annotated letters inside one block. -/
def AdjSame [Inhabited S] (K : ℕ) (stp : S → A → S) (b c : Gam A Q S K) : Prop :=
  (∀ s r, flL b s r = true → flL c s r = true)
  ∧ (∀ s r, flR b s r = true → flR c s r = true)
  ∧ (∀ s r, pr b s r = pr c s r)
  ∧ (∀ s, lp b s = lp c s)
  ∧ (∀ s r, r < 2 * K + 1 →
      ds c s r = (if wb c s r then stp (ds b s r) (lt c) else ds b s r))
  ∧ (∀ s r, flL b s r = false → flL c s r = true → lOf (pr c s r) = some (lt b))
  ∧ (∀ s r, flR b s r = false → flR c s r = true → rOf (pr c s r) = some (lt c))

/-- The conditions on two consecutive annotated letters separated by a block
boundary: the pair carried by the role `false` of the first letter is carried by
the role `true` of the second one, a new pair starts at the second letter, and
the pair carried by the role `true` of the first letter ends there. -/
def AdjSep [Inhabited S] (K : ℕ) (stp : S → A → S) (ini : S)
    (acc : PieceParam A Q → S → Prop) (b c : Gam A Q S K) : Prop :=
  (∀ r, flL b false r = true → flL c true r = true)
  ∧ (∀ r, flR b false r = true → flR c true r = true)
  ∧ (∀ r, pr b false r = pr c true r)
  ∧ lp b false = lp c true
  ∧ (∀ r, r < 2 * K + 1 →
      ds c true r = (if wb c true r then stp (ds b false r) (lt c) else ds b false r))
  ∧ (∀ r, flL b false r = false → flL c true r = true → lOf (pr c true r) = some (lt b))
  ∧ (∀ r, flR b false r = false → flR c true r = true → rOf (pr c true r) = some (lt c))
  ∧ (∀ r, r < 2 * K + 1 → ds c false r = (if wb c false r then stp ini (lt c) else ini))
  ∧ (∀ r, flL c false r = true → lOf (pr c false r) = some (lt b))
  ∧ (∀ r, flR c false r = true → rOf (pr c false r) = some (lt c))
  ∧ (∀ r, r < 2 * K + 1 → flL b true r = false → lOf (pr b true r) = some (lt b))
  ∧ (∀ r, r < 2 * K + 1 → flR b true r = false → rOf (pr b true r) = some (lt c))
  ∧ (∀ r, r < 2 * K + 1 → acc (pr b true r) (ds b true r))
  ∧ lp b true = false

/-- The conditions on the first annotated letter of the input. -/
def StartOK [Inhabited S] {B : Type} (M : TwoWay A B Q) (K : ℕ) (stp : S → A → S) (ini : S)
    (c : Gam A Q S K) : Prop :=
  sb c = true
  ∧ (∀ s r, r < 2 * K + 1 → ds c s r = (if wb c s r then stp ini (lt c) else ini))
  ∧ (∀ s r, flL c s r = true → lOf (pr c s r) = none)
  ∧ (∀ s r, flR c s r = true → rOf (pr c s r) = some (lt c))
  ∧ entOf (pr c true 0) = some M.init

/-- The conditions on the last annotated letter of the input. -/
def EndOK [Inhabited S] (K : ℕ) (acc : PieceParam A Q → S → Prop) (b : Gam A Q S K) : Prop :=
  (sa b = false →
    lp b true = true
    ∧ (∀ r, r < 2 * K + 1 → flL b true r = false → lOf (pr b true r) = some (lt b))
    ∧ (∀ r, flR b true r = false → rOf (pr b true r) = none)
    ∧ (∀ r, r < 2 * K + 1 → acc (pr b true r) (ds b true r)))
  ∧ (sa b = true →
    lp b false = true
    ∧ lp b true = false
    ∧ (∀ s r, r < 2 * K + 1 → flL b s r = false → lOf (pr b s r) = some (lt b))
    ∧ (∀ s r, flR b s r = false → rOf (pr b s r) = none)
    ∧ (∀ s r, r < 2 * K + 1 → acc (pr b s r) (ds b s r)))

/-- **The checking condition**, as a condition on a pair of consecutive
annotated letters. -/
def GoodP [Inhabited S] {B : Type} (M : TwoWay A B Q) (K : ℕ) (stp : S → A → S) (ini : S)
    (acc : PieceParam A Q → S → Prop) :
    Option (Gam A Q S K) → Option (Gam A Q S K) → Prop
  | none, none => True
  | none, some c => LetOK K c ∧ StartOK M K stp ini c
  | some b, none => EndOK K acc b
  | some b, some c =>
      LetOK K c ∧ sa b = false ∧
        (if sb c = true then AdjSep K stp ini acc b c else AdjSame K stp b c)

open Classical in
/-- The checking condition, as a Boolean function. -/
noncomputable def goodB [Inhabited S] {B : Type} (M : TwoWay A B Q) (K : ℕ) (stp : S → A → S)
    (ini : S) (acc : PieceParam A Q → S → Prop) :
    Option (Gam A Q S K) → Option (Gam A Q S K) → Bool :=
  fun x y => decide (GoodP M K stp ini acc x y)

lemma goodB_iff [Inhabited S] {B : Type} (M : TwoWay A B Q) (K : ℕ) (stp : S → A → S)
    (ini : S) (acc : PieceParam A Q → S → Prop) (x y : Option (Gam A Q S K)) :
    goodB M K stp ini acc x y = true ↔ GoodP M K stp ini acc x y := by
  classical
  show decide (GoodP M K stp ini acc x y) = true ↔ _
  exact decide_eq_true_iff

/-- **The language of the checking automaton**: the annotations all of whose
pairs of consecutive letters satisfy the checking condition. -/
noncomputable def ChkLang [Inhabited S] {B : Type} (M : TwoWay A B Q) (K : ℕ) (stp : S → A → S)
    (ini : S) (acc : PieceParam A Q → S → Prop) : Language (Gam A Q S K) :=
  {u | PairsOK (goodB M K stp ini acc) u}

/-- **The language of the checking automaton is regular.** -/
lemma isRegular_chkLang [Inhabited S] [Finite A] [Finite Q] [Finite S] {B : Type}
    (M : TwoWay A B Q) (K : ℕ) (stp : S → A → S) (ini : S)
    (acc : PieceParam A Q → S → Prop) :
    (ChkLang M K stp ini acc).IsRegular :=
  isRegular_pairsOK _

end Cond

end Chk

end TwoWay

end Lax916827Proofs.Transducers
