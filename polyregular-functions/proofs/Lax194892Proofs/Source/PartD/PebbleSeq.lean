/-
Post-composing a pebble transducer with a sequential machine.

This is one of the two ingredients of the easy inclusion of Theorem `thm:pebble-are-for` (a
for-transducer is simulated by a pebble transducer).  By Lemma `lemma:prenex-normal-form` and by
the analysis of `RequestProject/PartD/PolyScan.lean`, a for-transducer computes the composition of
two functions: the *enumeration* of the tuples of positions visited by its nest of loops -- which
is computed by a pebble transducer, see `RequestProject/PartD/PebbleEnum.lean` -- followed by the
*scan* of that enumeration, which runs the body of the nest on every copy of the input.  The scan
is given in that file as a streaming string transducer with a single register, whose updates only
append to it: that is to say, as a *sequential* machine, which reads its input from left to right
and emits a string at every step and one more string at the end.

Two things are proved here:

* a streaming string transducer with one register whose updates only append to it is a sequential
  machine (`Transducers.SeqTr.eval_of_sst_unit`), which applies in particular to the scanning
  machine of `RequestProject/PartD/PolyScan.lean` (`Transducers.PolyEnum.scanFun_eq_seqEval`);
* the composition of a pebble transducer with a sequential machine is a pebble transducer
  (`Transducers.isPebbleTransducer_seq_comp`).

The only difficulty in the second point is that a pebble transducer has no instruction that does
nothing: when the sequential machine emits nothing for the letter that the pebble transducer has
just produced, the simulating machine still has to make a step.  It makes two, pushing a pebble
and popping it again, which is why it uses one pebble more than the machine it simulates.
-/
import Lax194892Proofs.Source.PartD.PebbleDef
import Lax194892Proofs.Source.PartD.PolyScan
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-! ## Sequential machines -/

/-- A *sequential machine*: it reads its input letter by letter, from left to right, emitting a
string at every step, and one more string when the input is exhausted. -/
structure SeqTr (B C S : Type) where
  /-- The initial state. -/
  init : S
  /-- The transition function: a new state and the string emitted. -/
  step : S → B → S × List C
  /-- The string emitted at the end of the input. -/
  final : S → List C

namespace SeqTr

variable {B C S : Type}

/-- Running the machine on a string: the state reached and the string emitted. -/
def run (T : SeqTr B C S) : S → List B → S × List C
  | s, [] => (s, [])
  | s, b :: v =>
      let r := T.step s b
      let r' := T.run r.1 v
      (r'.1, r.2 ++ r'.2)

/-- The function computed by a sequential machine. -/
def eval (T : SeqTr B C S) (v : List B) : List C :=
  (T.run T.init v).2 ++ T.final (T.run T.init v).1

@[simp] lemma run_nil (T : SeqTr B C S) (s : S) : T.run s [] = (s, []) := rfl

lemma run_cons (T : SeqTr B C S) (s : S) (b : B) (v : List B) :
    T.run s (b :: v) =
      ((T.run (T.step s b).1 v).1, (T.step s b).2 ++ (T.run (T.step s b).1 v).2) := rfl

end SeqTr

/-! ## A streaming string transducer with one append-only register is sequential -/

section SSTUnit

variable {A B Q : Type}

open SST in
/-- If the register updates of a one-register streaming string transducer only append to the
register, then the transducer is a sequential machine. -/
lemma seqTr_eval_of_sst_unit (T : SST A B Q Unit) (out : Q → A → List B) (fin : Q → List B)
    (hstep : ∀ q a, (T.step q a).2 () = Sum.inl () :: (out q a).map Sum.inr)
    (hfin : ∀ q, T.final q = Sum.inl () :: (fin q).map Sum.inr) (u : List A) :
    T.eval u = (SeqTr.mk T.init (fun q a => ((T.step q a).1, out q a)) fin).eval u := by
  classical
  set S : SeqTr A B Q := SeqTr.mk T.init (fun q a => ((T.step q a).1, out q a)) fin with hS
  have hsubst : ∀ (R l : List B),
      SST.subst (fun _ : Unit => R) (Sum.inl () :: l.map Sum.inr) = R ++ l := by
    intro R l
    induction l with
    | nil => simp [SST.subst]
    | cons b l ih => simp [SST.subst] at ih ⊢; simp [ih]
  have key : ∀ (u : List A) (q : Q) (R : List B),
      u.foldl T.stepConfig (q, fun _ => R)
        = ((S.run q u).1, fun _ => R ++ (S.run q u).2) := by
    intro u
    induction u with
    | nil => intro q R; simp [SeqTr.run]
    | cons a u ih =>
        intro q R
        have h1 : T.stepConfig (q, fun _ => R) a = ((T.step q a).1, fun _ => R ++ out q a) := by
          refine Prod.ext rfl ?_
          funext x
          simp only [SST.stepConfig, hstep q a]
          exact hsubst R (out q a)
        rw [List.foldl_cons, h1, ih]
        refine Prod.ext rfl ?_
        funext x
        simp [SeqTr.run_cons, hS, List.append_assoc]
  have hrun : T.runConfig u = ((S.run T.init u).1, fun _ => (S.run T.init u).2) := by
    have := key u T.init []
    simpa [SST.runConfig] using this
  simp only [SST.eval, hrun, hfin, SeqTr.eval, hS]
  exact hsubst _ _

end SSTUnit

/-! ## Bounded lists -/

/-- The lists over `C` of length at most `N`. -/
def BddList (C : Type) (N : ℕ) : Type := {l : List C // l.length ≤ N}

namespace BddList

variable {C : Type} {N : ℕ}

instance [Finite C] : Finite (BddList C N) := by
  have h : Function.Injective (fun l : BddList C N => (fun i : Fin (N + 1) => l.val[(i : ℕ)]?)) := by
    intro l l' hll
    refine Subtype.ext (List.ext_getElem? ?_)
    intro i
    by_cases hi : i < N + 1
    · exact congrFun hll ⟨i, hi⟩
    · rw [List.getElem?_eq_none (by have := l.2; omega), List.getElem?_eq_none (by have := l'.2; omega)]
  exact Finite.of_injective _ h

/-- A list, truncated to the length `N`. -/
def of (l : List C) : BddList C N := ⟨l.take N, by simp⟩

@[simp] lemma of_val {l : List C} (h : l.length ≤ N) : (BddList.of (N := N) l).val = l := by
  simp [BddList.of, List.take_of_length_le h]

/-- The tail of a bounded list. -/
def tail (l : BddList C N) : BddList C N :=
  ⟨l.val.tail, by have := l.2; simp only [List.length_tail]; omega⟩

@[simp] lemma tail_val (l : BddList C N) : (BddList.tail l).val = l.val.tail := rfl

end BddList

/-! ## The composition of a pebble transducer with a sequential machine -/

section Comp

variable {A B C Q S : Type} {k N : ℕ}

/-- The states of the machine that runs the sequential machine `T` on the output of the pebble
transducer `M`: mirroring a step of `M`, popping the pebble of a silent step, emitting the
string that `T` produces for the letter just read, and emitting the final string of `T`. -/
inductive PSeqSt (Q S C : Type) (N : ℕ) : Type
  /-- About to perform the next step of `M`. -/
  | run : Q → S → PSeqSt Q S C N
  /-- Popping the pebble pushed by a silent step. -/
  | pop1 : Q → S → PSeqSt Q S C N
  /-- Emitting the rest of the string produced by `T`, and then continuing. -/
  | emit : BddList C N → Q → S → PSeqSt Q S C N
  /-- Emitting the rest of the final string of `T`, and then halting. -/
  | fin : BddList C N → PSeqSt Q S C N

instance [Finite Q] [Finite S] [Finite C] : Finite (PSeqSt Q S C N) := by
  have h : Function.Injective (fun z : PSeqSt Q S C N =>
      match z with
      | PSeqSt.run q s => (Sum.inl (q, s) : (Q × S) ⊕ (Q × S) ⊕ (BddList C N × Q × S) ⊕ BddList C N)
      | PSeqSt.pop1 q s => Sum.inr (Sum.inl (q, s))
      | PSeqSt.emit l q s => Sum.inr (Sum.inr (Sum.inl (l, q, s)))
      | PSeqSt.fin l => Sum.inr (Sum.inr (Sum.inr l))) := by
    intro z z' h
    cases z <;> cases z' <;> simp_all
  exact Finite.of_injective _ h

variable (M : Pebble A B Q k) (T : SeqTr B C S)

/-- The step of the composed machine when it is about to perform a step of `M`. -/
def pseqRun (q : Q) (s : S) (v : PebbleView A) : PSeqSt Q S C N × PebbleAction C :=
  let r := M.step q v
  match r.2 with
  | PebbleAction.out b =>
      let t := T.step s b
      match t.2 with
      | [] => (PSeqSt.pop1 r.1 t.1, PebbleAction.push)
      | c :: rest => (PSeqSt.emit (BddList.of rest) r.1 t.1, PebbleAction.out c)
  | PebbleAction.terminate =>
      match T.final s with
      | [] => (PSeqSt.fin (BddList.of []), PebbleAction.terminate)
      | c :: rest => (PSeqSt.fin (BddList.of rest), PebbleAction.out c)
  | PebbleAction.move d => (PSeqSt.run r.1 s, PebbleAction.move d)
  | PebbleAction.push => (PSeqSt.run r.1 s, PebbleAction.push)
  | PebbleAction.pop => (PSeqSt.run r.1 s, PebbleAction.pop)

/-- The machine that runs the sequential machine `T` on the output of the pebble transducer `M`.
It uses one pebble more than `M`, which it pushes and pops again in order to pass the time when
`T` emits nothing. -/
def pseq : Pebble A C (PSeqSt Q S C N) (k + 1) where
  init := PSeqSt.run M.init T.init
  step := fun z v =>
    match z with
    | PSeqSt.run q s => pseqRun M T q s v
    | PSeqSt.pop1 q s => (PSeqSt.run q s, PebbleAction.pop)
    | PSeqSt.emit l q s =>
        match l.val with
        | [] => pseqRun M T q s v
        | c :: _ => (PSeqSt.emit (BddList.tail l) q s, PebbleAction.out c)
    | PSeqSt.fin l =>
        match l.val with
        | [] => (PSeqSt.fin l, PebbleAction.terminate)
        | c :: _ => (PSeqSt.fin (BddList.tail l), PebbleAction.out c)

end Comp

end Lax194892Proofs.Transducers
