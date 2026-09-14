import Mathlib.Computability.Primrec.List
import Mathlib.Logic.Relation

/-!
---
title: Single-tape Turing machines as string rewriting
type: definition
---
A (possibly nondeterministic) single-tape Turing machine, presented as in
Sipser's *Introduction to the Theory of Computation*, Section 5.2: a finite
transition table with entries $\delta(q, a) = (r, b, \mathrm{dir})$, a start
state and an accept state. A *configuration* is a string $u\,q\,v$ over tape
symbols and states, where $u$ and $v$ are the tape contents to the left and to
the right of the head and $q$ is the current state, and one step of the machine
rewrites the configuration string locally around the state symbol:
$q\,a \to b\,r$ for a move to the right, and $c\,q\,a \to r\,c\,b$ for a move to
the left, which is possible only if there is a symbol $c$ to the left of the
head; a blank may be appended at the right-hand end, standing for the
infinitely many blanks that a written configuration suppresses. The machine
*accepts* the input $w$ if some configuration containing the accept state is
reachable from the starting configuration $q_0\,w$.

This is the combinatorial shape that the reduction to the Post correspondence
problem manipulates, so it is what the machine *is* here: a *string rewriting
system* — an alphabet, a finite list of rules $u \to v$ applied in arbitrary
context, and a list of symbols that may be appended on the right — whose rules
are read off the transition table.

# Formalization notes

Tape symbols and states are natural numbers, `0` being the blank. The alphabet
`Sym` in which configurations are written also carries the four auxiliary
symbols of Sipser's reduction (`#`, the start marker, `∗`, `◇`); they play no
role in the definition of the machine and are here only so that computation
histories and configurations are strings over one and the same alphabet.

The tape symbols and the states of a machine are the finitely many that its
table, its two distinguished states and the input mention. A move to the left
needs the symbol to the left of the head, so there is one left rule per tape
symbol `c`; the machine never moves its head off the left end. `Reaches` is
the reflexive transitive closure of the one-step relation. The `Primcodable`
instance encodes a machine by its table and its two states, so that decision
problems about machines can be stated with mathlib's `ComputablePred`.
-/

namespace Lax251941.TuringMachines

/-- The symbols in which configurations of a Turing machine, and the strings of
Sipser's reduction, are written. -/
inductive Sym where
  /-- A tape symbol; `Sym.tape 0` is the blank. -/
  | tape : ℕ → Sym
  /-- A state of the machine. -/
  | state : ℕ → Sym
  /-- The separator `#` between consecutive configurations of a history. -/
  | hash : Sym
  /-- The marker opening a computation history. -/
  | start : Sym
  /-- The auxiliary symbol `∗` of the reduction. -/
  | star : Sym
  /-- The auxiliary symbol `◇` of the reduction. -/
  | diamond : Sym
  deriving DecidableEq, Repr

/-- A string rewriting system: an alphabet, a finite list of rewriting rules
`u → v` applied in arbitrary context, and a list of symbols that may be appended
at the right end of a string. -/
structure SRS (α : Type*) where
  /-- The alphabet. -/
  alphabet : List α
  /-- The rewriting rules `u → v`. -/
  rules : List (List α × List α)
  /-- Symbols that may be appended at the right-hand end of a string. -/
  ext : List α

/-- One application of a rule, in a context `l _ r`. -/
inductive StepRule {α : Type*} (rules : List (List α × List α)) : List α → List α → Prop
  | mk (l u v r : List α) : (u, v) ∈ rules → StepRule rules (l ++ u ++ r) (l ++ v ++ r)

/-- One step of a rewriting system: a rule application, or appending one of the
designated symbols on the right. -/
inductive Step {α : Type*} (S : SRS α) : List α → List α → Prop
  | rule {a b : List α} : StepRule S.rules a b → Step S a b
  | ext {c : List α} {x : α} : x ∈ S.ext → Step S c (c ++ [x])

/-- Reachability: the reflexive transitive closure of `Step`. -/
def Reaches {α : Type*} (S : SRS α) : List α → List α → Prop := Relation.ReflTransGen (Step S)

/-- A single-tape Turing machine: a transition table whose entry `(q, a, r, b, dir)`
means `δ(q, a) = (r, b, dir)`, `dir = true` being a move to the right and
`dir = false` a move to the left, together with a start state and an accept
state. -/
structure TM where
  /-- The transition table. -/
  trans : List (ℕ × ℕ × ℕ × ℕ × Bool)
  /-- The start state. -/
  q0 : ℕ
  /-- The accept state. -/
  qacc : ℕ

namespace TM

variable (M : TM) (w : List ℕ)

/-- The tape symbols of a machine run on `w`: the blank, the letters of `w`, and
the symbols read or written by the table. -/
def tapeSyms : List ℕ :=
  0 :: (w ++ M.trans.map (fun x => x.2.1) ++ M.trans.map (fun x => x.2.2.2.1))

/-- The states of a machine: the start state, the accept state and the states of
the table. -/
def states : List ℕ :=
  M.q0 :: M.qacc :: (M.trans.map (fun x => x.1) ++ M.trans.map (fun x => x.2.2.1))

/-- The alphabet in which the configurations of a run on `w` are written. -/
def alphabet : List Sym :=
  (M.tapeSyms w).map Sym.tape ++ M.states.map Sym.state

/-- The rewriting rules `q a → b r` of the moves to the right. -/
def rightRules : List (List Sym × List Sym) :=
  M.trans.filterMap fun x =>
    if x.2.2.2.2 then
      some ([Sym.state x.1, Sym.tape x.2.1], [Sym.tape x.2.2.2.1, Sym.state x.2.2.1])
    else none

/-- The rewriting rules `c q a → r c b` of the moves to the left, one for every
tape symbol `c` to the left of the head. -/
def leftRules : List (List Sym × List Sym) :=
  (M.tapeSyms w).flatMap fun c =>
    M.trans.filterMap fun x =>
      if x.2.2.2.2 then none
      else some ([Sym.tape c, Sym.state x.1, Sym.tape x.2.1],
        [Sym.state x.2.2.1, Sym.tape c, Sym.tape x.2.2.2.1])

/-- The rewriting rules describing the single steps of the machine. -/
def transRules : List (List Sym × List Sym) := M.rightRules ++ M.leftRules w

/-- The rewriting system of the machine on the input `w`: its step rules, with a
blank appendable on the right. -/
def machineSRS : SRS Sym where
  alphabet := M.alphabet w
  rules := M.transRules w
  ext := [Sym.tape 0]

/-- The starting configuration `q₀ w`. -/
def startCfg : List Sym := Sym.state M.q0 :: w.map Sym.tape

/-- The machine accepts `w` if a configuration containing the accept state is
reachable from the starting configuration. -/
def Accepts : Prop :=
  ∃ C, Reaches (M.machineSRS w) (M.startCfg w) C ∧ Sym.state M.qacc ∈ C

end TM

/-- A machine is encoded by its transition table and its two distinguished states.
-/
def tmEquiv : TM ≃ List (ℕ × ℕ × ℕ × ℕ × Bool) × ℕ × ℕ where
  toFun M := (M.trans, M.q0, M.qacc)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := by rintro ⟨t, a, b⟩; rfl
  right_inv := by rintro ⟨t, a, b⟩; rfl

instance : Primcodable TM := Primcodable.ofEquiv _ tmEquiv

end Lax251941.TuringMachines
