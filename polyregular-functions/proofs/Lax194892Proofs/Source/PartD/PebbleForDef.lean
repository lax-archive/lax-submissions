/-
Part D: a for-transducer in prenex form is simulated by a pebble transducer.

This is the easy inclusion of Theorem `thm:pebble-are-for`: "a for-transducer can easily be
simulated by a pebble transducer, with one pebble for each nested for loop, and with the state
used to store the values of the Boolean variables and the currently executed instruction".

By Lemma `lemma:prenex-normal-form` it is enough to simulate a program in prenex form, a nest of
loops with a loop-free body -- which outputs at most one letter per iteration -- followed by a
loop-free epilogue.  The simulating machine uses one pebble per loop of the nest, plus one extra
pebble that stays at the position `0` for ever: that pebble plays the role of the position
variables of the body that the nest does not bind (they keep their initial value `0`), and it
also provides the first letter of the input, which is all that the epilogue can see.

The one thing that the view of a stack of pebbles does not tell the machine is the *order* of the
pebbles -- it only tells which of them are at the same place.  The machine therefore keeps the
order in its state, as a matrix of bits, and updates it whenever the topmost pebble moves.  The
new column of the matrix needs to know which pebbles sit at the position that the topmost pebble
has just moved to, which is information that only the *next* view provides; the state therefore
also records the move that has just been made (`PSt.pend`), and every step begins by repairing
the matrix (`PebFor.fixOrd`) with the help of the view it is given.

This file contains the machine and the elementary facts about reading a view; its correctness is
proved in `RequestProject/PartD/PebbleForRun.lean`.
-/
import Lax194892Proofs.Source.PartD.PebbleSeq
import Lax194892Proofs.Source.PartD.ForPrenexTop
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebFor

open PolyEnum

variable {A B : Type} {k : ℕ}

/-! ## Reading the view of a stack of pebbles

Throughout, the stack of the simulating machine is `0 :: ps`, where `ps` lists the positions of
the pebbles of the loops that are currently running; the pebble at the bottom is the one that
stays at `0`.  The variable `i` (a number `≤ k`, where `k` is the number of loops) is read at the
stack index `i + 1` if the loop `i` is running, and at the stack index `0` otherwise -- which is
the right thing for the variables that the nest does not bind, whose value is `0`. -/

/-- The default entry of a view. -/
def vdef (A : Type) : (Option A × Option A) × List Bool := ((none, none), [])

/-- The index, in the stack, of the pebble that gives the value of the variable `i`. -/
def sIdx (v : PebbleView A) (i : ℕ) : ℕ := if i + 1 < v.length then i + 1 else 0

/-- The letter of the input at the position of the variable `i`. -/
def letAt (v : PebbleView A) (i : ℕ) : Option A := (v.getD (sIdx v i) (vdef A)).1.2

/-- Whether the variables `i` and `x` are at the same position. -/
def coin (v : PebbleView A) (x i : ℕ) : Bool :=
  ((v.getD (sIdx v x) (vdef A)).2).getD (sIdx v i) false

/-- The position of the variable `i`, for a stack `0 :: ps`. -/
def posOf (ps : List ℕ) (i : ℕ) : ℕ := ps.getD i 0

section View

variable {w : List A} {ps : List ℕ}

lemma viewOf_length (w : List A) (st : List ℕ) : (viewOf w st).length = st.length := by
  simp [viewOf]

lemma viewOf_getD {st : List ℕ} {s : ℕ} (hs : s < st.length) :
    (viewOf w st).getD s (vdef A)
      = ((if st.getD s 0 = 0 then none else w[st.getD s 0 - 1]?, w[st.getD s 0]?),
          st.map (fun q => decide (q = st.getD s 0))) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [viewOf, List.getElem?_map, List.getElem?_eq_getElem hs]
  rfl

lemma sIdx_lt (v : PebbleView A) (i : ℕ) (hv : 0 < v.length) : sIdx v i < v.length := by
  unfold sIdx
  split <;> omega

lemma sIdx_stack (w : List A) (ps : List ℕ) (i : ℕ) :
    (0 :: ps).getD (sIdx (viewOf w (0 :: ps)) i) 0 = posOf ps i := by
  have hlen : (viewOf w (0 :: ps)).length = ps.length + 1 := by simp [viewOf_length]
  unfold sIdx posOf
  rw [hlen]
  by_cases h : i + 1 < ps.length + 1
  · rw [if_pos h]
    simp only [List.getD_cons_succ]
  · rw [if_neg h]
    have hnone : ps[i]? = none := List.getElem?_eq_none (by omega)
    simp [List.getD_eq_getElem?_getD, hnone]

/-- The letter that the machine reads for the variable `i` is the letter at its position. -/
lemma letAt_viewOf (w : List A) (ps : List ℕ) (i : ℕ) :
    letAt (viewOf w (0 :: ps)) i = w[posOf ps i]? := by
  have hlen : (viewOf w (0 :: ps)).length = ps.length + 1 := by simp [viewOf_length]
  have hs : sIdx (viewOf w (0 :: ps)) i < (0 :: ps).length := by
    have := sIdx_lt (viewOf w (0 :: ps)) i (by omega)
    simpa [hlen] using this
  unfold letAt
  rw [viewOf_getD hs, sIdx_stack w ps i]

/-- The coincidence bits that the machine reads are the equalities of the positions. -/
lemma coin_viewOf (w : List A) (ps : List ℕ) (x i : ℕ) :
    coin (viewOf w (0 :: ps)) x i = decide (posOf ps i = posOf ps x) := by
  have hlen : (viewOf w (0 :: ps)).length = ps.length + 1 := by simp [viewOf_length]
  have hsx : sIdx (viewOf w (0 :: ps)) x < (0 :: ps).length := by
    have := sIdx_lt (viewOf w (0 :: ps)) x (by omega)
    simpa [hlen] using this
  have hsi : sIdx (viewOf w (0 :: ps)) i < (0 :: ps).length := by
    have := sIdx_lt (viewOf w (0 :: ps)) i (by omega)
    simpa [hlen] using this
  unfold coin
  rw [viewOf_getD hsx]
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hsi]
  simp only [Option.map_some, Option.getD_some]
  rw [show (0 :: ps)[sIdx (viewOf w (0 :: ps)) i] = (0 :: ps).getD (sIdx (viewOf w (0 :: ps)) i) 0 from
      (List.getD_eq_getElem _ _ hsi).symm]
  rw [sIdx_stack w ps i, sIdx_stack w ps x]

end View

/-! ## Reading a position out of a stack -/

lemma posOf_of_length_le {ps : List ℕ} {i : ℕ} (h : ps.length ≤ i) : posOf ps i = 0 := by
  unfold posOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma posOf_snoc (pre : List ℕ) (p i : ℕ) :
    posOf (pre ++ [p]) i = if i = pre.length then p else posOf pre i := by
  rcases lt_trichotomy i pre.length with h | h | h
  · rw [if_neg (by omega)]
    unfold posOf
    rw [List.getD_append _ _ _ _ h]
  · subst h
    rw [if_pos rfl]
    unfold posOf
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp
  · rw [if_neg (by omega), posOf_of_length_le (by simp; omega),
      posOf_of_length_le (by omega)]

lemma posOf_snoc_zero (ps : List ℕ) (i : ℕ) : posOf (ps ++ [0]) i = posOf ps i := by
  rw [posOf_snoc]
  by_cases h : i = ps.length
  · rw [if_pos h, h, posOf_of_length_le (le_refl _)]
  · rw [if_neg h]

/-! ## The output length of a loop-free program -/

/-- A syntactic bound on the number of letters that one execution of a loop-free program can
produce. -/
def outBound : ForProg A B → ℕ
  | ForProg.skip => 0
  | ForProg.output _ => 1
  | ForProg.assign _ _ => 0
  | ForProg.seq P Q => outBound P + outBound Q
  | ForProg.ite _ P Q => max (outBound P) (outBound Q)
  | ForProg.loop _ _ _ => 0

lemma length_exec_le {P : ForProg A B} (hP : P.LoopFree) (w : List A) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) : ((ForProg.exec w P pos bv).2).length ≤ outBound P := by
  induction P generalizing bv with
  | skip => simp [ForProg.exec, outBound]
  | output b => simp [ForProg.exec, outBound]
  | assign i b => simp [ForProg.exec, outBound]
  | seq P Q ihP ihQ =>
      have h := hP
      simp only [ForProg.LoopFree] at h
      simp only [ForProg.exec, outBound, List.length_append]
      exact Nat.add_le_add (ihP h.1 _) (ihQ h.2 _)
  | ite t P Q ihP ihQ =>
      have h := hP
      simp only [ForProg.LoopFree] at h
      simp only [ForProg.exec, outBound]
      by_cases ht : ForTest.Holds w pos bv t
      · rw [if_pos ht]; exact le_trans (ihP h.1 _) (le_max_left _ _)
      · rw [if_neg ht]; exact le_trans (ihQ h.2 _) (le_max_right _ _)
  | loop d x P _ => exact absurd hP (by simp [ForProg.LoopFree])

/-! ## The machine -/

/-- The phases of the simulating machine. -/
inductive Ph (B : Type) (k N : ℕ) : Type
  /-- Pushing the pebble that stays at the position `0`. -/
  | start : Ph B k N
  /-- Starting the loop `j` (or running the body, if `j = k`). -/
  | enter : Fin (k + 1) → Ph B k N
  /-- The pebble of the loop `j` has just been pushed, at the position `0`. -/
  | init : Fin (k + 1) → Ph B k N
  /-- Walking the pebble of the backward loop `j` to the last position. -/
  | seek : Fin (k + 1) → Ph B k N
  /-- Checking whether the forward loop `j` is over. -/
  | chk : Fin (k + 1) → Ph B k N
  /-- Advancing the loop `j`. -/
  | adv : Fin (k + 1) → Ph B k N
  /-- Running the epilogue. -/
  | epiStart : Ph B k N
  /-- Emitting the rest of the output of the epilogue. -/
  | epi : BddList B N → Ph B k N

instance {B : Type} {k N : ℕ} [Finite B] : Finite (Ph B k N) := by
  have h : Function.Injective (fun z : Ph B k N =>
      match z with
      | Ph.start => (Sum.inl 0 : (Fin 2) ⊕ (Fin 5 × Fin (k + 1)) ⊕ BddList B N)
      | Ph.enter j => Sum.inr (Sum.inl (0, j))
      | Ph.init j => Sum.inr (Sum.inl (1, j))
      | Ph.seek j => Sum.inr (Sum.inl (2, j))
      | Ph.chk j => Sum.inr (Sum.inl (3, j))
      | Ph.adv j => Sum.inr (Sum.inl (4, j))
      | Ph.epiStart => Sum.inl 1
      | Ph.epi l => Sum.inr (Sum.inr l)) := by
    intro z z' h
    cases z <;> cases z' <;> simp_all
  exact Finite.of_injective _ h

/-- The state of the simulating machine. -/
structure PSt (A B : Type) (k m N : ℕ) where
  /-- The values of the Boolean variables of the for-transducer. -/
  bv : Fin m → Bool
  /-- The order of the positions of the variables. -/
  ord : Fin (k + 1) → Fin (k + 1) → Bool
  /-- The move that has just been made, whose effect on `ord` is still to be recorded. -/
  pend : Option (Fin (k + 1) × Bool)
  /-- The phase. -/
  ph : Ph B k N

instance {A B : Type} {k m N : ℕ} [Finite B] : Finite (PSt A B k m N) := by
  have h : Function.Injective (fun q : PSt A B k m N => (q.bv, q.ord, q.pend, q.ph)) := by
    intro q q' h
    cases q; cases q'
    simp_all
  exact Finite.of_injective _ h

section Machine

/-- The direction of the loop `j` of the nest. -/
def dirOf (L : List (Bool × ℕ)) (j : ℕ) : Bool := (L.getD j (true, 0)).1

/-- The successor of a variable index, capped at `k`. -/
def fsucc (k : ℕ) (j : Fin (k + 1)) : Fin (k + 1) := ⟨min ((j : ℕ) + 1) k, by omega⟩

/-- The predecessor of a variable index. -/
def fpred (k : ℕ) (j : Fin (k + 1)) : Fin (k + 1) := ⟨(j : ℕ) - 1, by omega⟩

/-- The last variable index of a loop of the nest. -/
def flast (k : ℕ) : Fin (k + 1) := ⟨k - 1, by omega⟩

/-- Repairing the order matrix after the move recorded in `pend`. -/
def fixOrd (k : ℕ) (o : Fin (k + 1) → Fin (k + 1) → Bool) (pd : Option (Fin (k + 1) × Bool))
    (v : PebbleView A) : Fin (k + 1) → Fin (k + 1) → Bool :=
  match pd with
  | none => o
  | some (x, dir) => fun i j =>
      if i = x then
        (if j = x then true
          else if dir then !(o j x) else (o x j || coin v (x : ℕ) (j : ℕ)))
      else if j = x then
        (if dir then (o i x || coin v (x : ℕ) (i : ℕ)) else !(o x i))
      else o i j

lemma fixOrd_none (k : ℕ) (o : Fin (k + 1) → Fin (k + 1) → Bool) (v : PebbleView A) :
    fixOrd k o none v = o := rfl

lemma fixOrd_some (k : ℕ) (o : Fin (k + 1) → Fin (k + 1) → Bool) (x : Fin (k + 1)) (dir : Bool)
    (v : PebbleView A) (i j : Fin (k + 1)) :
    fixOrd k o (some (x, dir)) v i j =
      (if i = x then
        (if j = x then true
          else if dir then !(o j x) else (o x j || coin v (x : ℕ) (j : ℕ)))
      else if j = x then
        (if dir then (o i x || coin v (x : ℕ) (i : ℕ)) else !(o x i))
      else o i j) := rfl

/-- The order matrix after the pebble of the variable `x` has been popped, so that the variable
returns to the position `0`. -/
def popFix (k : ℕ) (o : Fin (k + 1) → Fin (k + 1) → Bool) (x : Fin (k + 1)) (v : PebbleView A) :
    Fin (k + 1) → Fin (k + 1) → Bool :=
  fun i j => if i = x then true else if j = x then coin v k (i : ℕ) else o i j

/-- What the machine knows about the current tuple of positions. -/
noncomputable def blkOf (k : ℕ) (o : Fin (k + 1) → Fin (k + 1) → Bool) (v : PebbleView A) :
    Option (Blk A k) :=
  match letAt v k with
  | none => none
  | some a₀ => some ⟨fun i => (letAt v (i : ℕ)).getD a₀, o⟩

/-- Running the epilogue and emitting its output. -/
noncomputable def epiAct (k m N : ℕ) (epilogue : ForProg A B) (bv : Fin m → Bool)
    (o : Fin (k + 1) → Fin (k + 1) → Bool) (v : PebbleView A) :
    PSt A B k m N × PebbleAction B :=
  match (ForProg.exec (letAt v k).toList epilogue (fun _ => 0) (extBV m bv)).2 with
  | [] => (⟨bv, o, none, Ph.epiStart⟩, PebbleAction.terminate)
  | b :: rest => (⟨bv, o, none, Ph.epi (BddList.of rest)⟩, PebbleAction.out b)

/-- Popping the pebble of the loop `j`, whose iterations are over. -/
def popAct (k m N : ℕ) (j : Fin (k + 1)) (bv : Fin m → Bool)
    (o : Fin (k + 1) → Fin (k + 1) → Bool) (v : PebbleView A) :
    PSt A B k m N × PebbleAction B :=
  (⟨bv, popFix k o j v, none,
      if (j : ℕ) = 0 then Ph.epiStart else Ph.adv (fpred k j)⟩, PebbleAction.pop)

/-- Advancing the loop `j` to its next position, or ending it. -/
def advAct (k m N : ℕ) (L : List (Bool × ℕ)) (j : Fin (k + 1)) (bv : Fin m → Bool)
    (o : Fin (k + 1) → Fin (k + 1) → Bool) (v : PebbleView A) :
    PSt A B k m N × PebbleAction B :=
  if dirOf L (j : ℕ) then
    (⟨bv, o, some (j, true), Ph.chk j⟩, PebbleAction.move true)
  else
    if coin v k (j : ℕ) then popAct k m N j bv o v
    else (⟨bv, o, some (j, false), Ph.enter (fsucc k j)⟩, PebbleAction.move false)

/-- What the machine does once the body has been run: it advances the innermost loop, or -- if
there is no loop at all -- runs the epilogue. -/
noncomputable def afterAct (k m N : ℕ) (L : List (Bool × ℕ)) (epilogue : ForProg A B)
    (bv : Fin m → Bool) (o : Fin (k + 1) → Fin (k + 1) → Bool) (v : PebbleView A) :
    PSt A B k m N × PebbleAction B :=
  if k = 0 then epiAct k m N epilogue bv o v else advAct k m N L (flast k) bv o v

/-- The phase that the machine is in once the body has been run and its letter emitted. -/
def afterPh (B : Type) (k N : ℕ) : Ph B k N := if k = 0 then Ph.epiStart else Ph.adv (flast k)

/-- Running the body of the nest on the current tuple of positions. -/
noncomputable def bodyAct (k m N : ℕ) (L : List (Bool × ℕ)) (body epilogue : ForProg A B)
    (vf : ℕ → Fin (k + 1)) (bv : Fin m → Bool) (o : Fin (k + 1) → Fin (k + 1) → Bool)
    (v : PebbleView A) : PSt A B k m N × PebbleAction B :=
  match (bodyRun k m body vf bv (blkOf k o v)).2 with
  | [] => afterAct k m N L epilogue (resBV m (bodyRun k m body vf bv (blkOf k o v)).1) o v
  | b :: _ => (⟨resBV m (bodyRun k m body vf bv (blkOf k o v)).1, o, none, afterPh B k N⟩,
      PebbleAction.out b)

/-- Starting the loop `j`, or running the body if all the loops are running. -/
noncomputable def enterAct (k m N : ℕ) (L : List (Bool × ℕ)) (body epilogue : ForProg A B)
    (vf : ℕ → Fin (k + 1)) (j : Fin (k + 1)) (bv : Fin m → Bool)
    (o : Fin (k + 1) → Fin (k + 1) → Bool) (v : PebbleView A) :
    PSt A B k m N × PebbleAction B :=
  if (j : ℕ) = k then bodyAct k m N L body epilogue vf bv o v
  else (⟨bv, o, none, Ph.init j⟩, PebbleAction.push)

/-- One step of the simulating machine. -/
noncomputable def stepFn (k m N : ℕ) (L : List (Bool × ℕ)) (body epilogue : ForProg A B)
    (vf : ℕ → Fin (k + 1)) (q : PSt A B k m N) (v : PebbleView A) :
    PSt A B k m N × PebbleAction B :=
  let o := fixOrd k q.ord q.pend v
  match q.ph with
  | Ph.start => (⟨q.bv, o, none, Ph.enter 0⟩, PebbleAction.push)
  | Ph.enter j => enterAct k m N L body epilogue vf j q.bv o v
  | Ph.init j =>
      match letAt v (j : ℕ) with
      | none => popAct k m N j q.bv o v
      | some _ =>
          if dirOf L (j : ℕ) then enterAct k m N L body epilogue vf (fsucc k j) q.bv o v
          else (⟨q.bv, o, some (j, true), Ph.seek j⟩, PebbleAction.move true)
  | Ph.seek j =>
      match letAt v (j : ℕ) with
      | none => (⟨q.bv, o, some (j, false), Ph.enter (fsucc k j)⟩, PebbleAction.move false)
      | some _ => (⟨q.bv, o, some (j, true), Ph.seek j⟩, PebbleAction.move true)
  | Ph.chk j =>
      match letAt v (j : ℕ) with
      | none => popAct k m N j q.bv o v
      | some _ => enterAct k m N L body epilogue vf (fsucc k j) q.bv o v
  | Ph.adv j => advAct k m N L j q.bv o v
  | Ph.epiStart => epiAct k m N epilogue q.bv o v
  | Ph.epi l =>
      match l.val with
      | [] => (⟨q.bv, o, none, Ph.epi l⟩, PebbleAction.terminate)
      | b :: _ => (⟨q.bv, o, none, Ph.epi (BddList.tail l)⟩, PebbleAction.out b)

/-- The machine that simulates the nest of loops `L` with the loop-free body `body` and the
loop-free epilogue `epilogue`. -/
noncomputable def peb (k m N : ℕ) (L : List (Bool × ℕ)) (body epilogue : ForProg A B)
    (vf : ℕ → Fin (k + 1)) : Pebble A B (PSt A B k m N) (k + 1) where
  init := ⟨fun _ => false, fun _ _ => true, none, Ph.start⟩
  step := stepFn k m N L body epilogue vf

end Machine

end PebFor

end Lax194892Proofs.Transducers
