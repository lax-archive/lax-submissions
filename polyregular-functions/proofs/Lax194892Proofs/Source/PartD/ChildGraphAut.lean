/-
**The two-pebble transducer that outputs the children of a child configuration graph.**

Claim `claim:from-child-configuration-graph-to-children` of *Transducers* (M. Bojańczyk) asks for a
for-transducer which inputs the string representation of a child configuration graph and outputs
the concatenation of the string representations of the children.  The book proves it by the
induction on the width of the graph used for Lemma `lem:output-of-snake-graph-is-regular`; the
difference with that lemma, as the book says, is that "for each vertex in the child configuration
graph we need to output the entire child configuration, which requires producing a copy of the
input string.  In particular, the transformation has quadratic output size."

The route taken here produces the same function with a **two-pebble transducer**, which is
equivalent to a for-transducer by Theorem `thm:pebble-are-for`
(`Transducers.pebble_iff_forTransducer`).  The bottom pebble walks along the edges of the graph,
one vertex at a time, and for each vertex the top pebble sweeps the input from left to right and
prints the string representation of the corresponding child.  The quadratic output size is exactly
what two nested pebbles provide.

The machine works in the following phases.

* `start`: push the first pebble.
* `chk ok`: sweep the first pebble to the right, running the local consistency test `CG.pairOK` on
  every pair of adjacent letters.  When the end of the input is reached, the machine gives up (and
  outputs nothing) unless the test succeeded everywhere.  The test guarantees that the walk along
  the edges terminates, so that the machine halts on *every* input, as the definition of a
  transducer requires.
* `find`: sweep the first pebble back to the left until a vertex marked as the first child is
  found; give up if there is none.
* `prt q`, `mv q`: with the first pebble on the column of the current child and the second pebble
  sweeping the input, print the string representation of the current child.
* `adv q`: the second pebble has been popped; read the outgoing edge of the current vertex and move
  the first pebble to the column of the next child, or halt if there is no outgoing edge.
* `ent q`: the first pebble has just been moved; halt if it has left the input, and otherwise start
  printing the next child.
-/
import Lax194892Proofs.Source.PartD.ChildGraph
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CG

/-- The phases of the machine; see the header of this file. -/
inductive PSt (Q : Type) : Type
  | start
  | chk (ok : Bool)
  | find
  | prt (q : Q)
  | mv (q : Q)
  | adv (q : Q)
  | ent (q : Q)
  | dead

instance {Q : Type} [Finite Q] : Finite (PSt Q) := by
  have h : Function.Injective (fun s : PSt Q => match s with
      | PSt.start => ((none, false, 0) : Option Q × Bool × Fin 4)
      | PSt.chk b => (none, b, 1)
      | PSt.find => (none, false, 2)
      | PSt.dead => (none, false, 3)
      | PSt.prt q => (some q, false, 0)
      | PSt.mv q => (some q, false, 1)
      | PSt.adv q => (some q, false, 2)
      | PSt.ent q => (some q, false, 3)) := by
    intro a b hab
    cases a <;> cases b <;> simp_all
  exact Finite.of_injective _ h

variable {A Q : Type} {k : ℕ}

/-- The two input letters adjacent to the `i`-th pebble of a view. -/
def letsAt (V : PebbleView (CGLetter A Q k)) (i : ℕ) :
    Option (CGLetter A Q k) × Option (CGLetter A Q k) :=
  match V[i]? with
  | none => (none, none)
  | some e => e.1

/-- Whether the first pebble sits in the same gap as the second one. -/
def coin (V : PebbleView (CGLetter A Q k)) : Bool :=
  match V[1]? with
  | none => false
  | some e => (e.2[0]?).getD false

open Classical in
/-- The state marked as the first child in a letter, if there is one. -/
noncomputable def pickSrc (s : Q → Bool) : Option Q :=
  if h : ∃ q, s q = true then some h.choose else none

lemma pickSrc_eq_some {s : Q → Bool} {q : Q} (h : pickSrc s = some q) : s q = true := by
  unfold pickSrc at h
  split at h
  · rename_i hex
    rw [Option.some.injEq] at h
    rw [← h]
    exact hex.choose_spec
  · exact absurd h (by simp)

lemma pickSrc_eq_none {s : Q → Bool} (h : pickSrc s = none) (q : Q) : s q = false := by
  unfold pickSrc at h
  split at h
  · exact absurd h (by simp)
  · rename_i hex
    push_neg at hex
    simpa using hex q

lemma pickSrc_of_unique {s : Q → Bool} {q : Q} (hq : s q = true)
    (huniq : ∀ q', s q' = true → q' = q) : pickSrc s = some q := by
  cases h : pickSrc s with
  | none => exact absurd hq (by rw [pickSrc_eq_none h q]; simp)
  | some q' => rw [huniq q' (pickSrc_eq_some h)]

open Classical in
/-- **The transition function of the machine**; see the header of this file. -/
noncomputable def cgStep : PSt Q → PebbleView (CGLetter A Q k) →
    PSt Q × PebbleAction (ConfLetter A Q k)
  | PSt.start, _ => (PSt.chk true, PebbleAction.push)
  | PSt.chk ok, V =>
      match (letsAt V 0).2 with
      | none =>
          if ok && pairOK (letsAt V 0).1 none && ((letsAt V 0).1).isSome then
            (PSt.find, PebbleAction.move false)
          else (PSt.dead, PebbleAction.terminate)
      | some c =>
          (PSt.chk (ok && pairOK (letsAt V 0).1 (some c)), PebbleAction.move true)
  | PSt.find, V =>
      match (letsAt V 0).2 with
      | none => (PSt.dead, PebbleAction.terminate)
      | some c =>
          match pickSrc c.src with
          | some q => (PSt.prt q, PebbleAction.push)
          | none =>
              if ((letsAt V 0).1).isSome then (PSt.find, PebbleAction.move false)
              else (PSt.dead, PebbleAction.terminate)
  | PSt.prt q, V =>
      match (letsAt V 1).2 with
      | none => (PSt.adv q, PebbleAction.pop)
      | some c =>
          (PSt.mv q,
            PebbleAction.out (q, c.lett, fun i => c.peb i || (decide (i = c.nid) && coin V)))
  | PSt.mv q, _ => (PSt.prt q, PebbleAction.move true)
  | PSt.adv q, V =>
      match (letsAt V 0).2 with
      | none => (PSt.dead, PebbleAction.terminate)
      | some c =>
          match c.nxt q with
          | none => (PSt.dead, PebbleAction.terminate)
          | some (q', none) => (PSt.prt q', PebbleAction.push)
          | some (q', some true) => (PSt.ent q', PebbleAction.move true)
          | some (q', some false) =>
              if ((letsAt V 0).1).isSome then (PSt.ent q', PebbleAction.move false)
              else (PSt.dead, PebbleAction.terminate)
  | PSt.ent q, V =>
      match (letsAt V 0).2 with
      | none => (PSt.dead, PebbleAction.terminate)
      | some _ => (PSt.prt q, PebbleAction.push)
  | PSt.dead, _ => (PSt.dead, PebbleAction.terminate)

/-- **The machine of Claim `claim:from-child-configuration-graph-to-children`.** -/
noncomputable def cgAut : Pebble (CGLetter A Q k) (ConfLetter A Q k) (PSt Q) 2 where
  init := PSt.start
  step := cgStep

/-! ## Reading the view -/

variable (u : List (CGLetter A Q k))

@[simp] lemma letsAt_one (p : ℕ) : letsAt (viewOf u [p]) 0 = (leftLet u p, u[p]?) := by
  simp [letsAt, viewOf, leftLet]

@[simp] lemma letsAt_two_zero (p j : ℕ) :
    letsAt (viewOf u [p, j]) 0 = (leftLet u p, u[p]?) := by
  simp [letsAt, viewOf, leftLet]

@[simp] lemma letsAt_two_one (p j : ℕ) :
    letsAt (viewOf u [p, j]) 1 = (leftLet u j, u[j]?) := by
  simp [letsAt, viewOf, leftLet]

@[simp] lemma coin_two (p j : ℕ) : coin (viewOf u [p, j]) = decide (p = j) := by
  simp [coin, viewOf]

end CG

end Lax194892Proofs.Transducers
