/-
**The automaton that checks reachability between two encoded configurations.**

This is the technical heart of Lemma `lem:reachability-pebble-automaton` and of Claim
`claim:reachability-basic-run` of *Transducers* (M. Bojańczyk).  Given a pebble transducer `M` with
`k` pebbles, a floor `ℓ` and two states `q₁`, `q₂`, we build a pebble *automaton* with `k+1` pebbles
which reads the string representation `PebEnc.pairEnc q₁ q₂ sts stt w` of a pair of configurations
(`RequestProject/PartD/PebEnc.lean`) and answers `true` exactly when there is a run of `M` from
`(q₁, sts)` to `(q₂, stt)` all of whose configurations have stack height at least `ℓ`.

Since pebble automata recognise regular languages (`Transducers.pebbleAut_answers_isRegular`), this
gives the regularity -- equivalently, by Theorem `thm:mso-logic-languages`, the mso-definability --
of reachability between configurations, which is what the two results of the book assert.

The automaton runs in four phases.

* `start`  -- push the single pebble that the first two phases use;
* `sweep`  -- walk to the end of the encoding, collecting in the state which pebble indices occur
  in the source annotation and in the target annotation;
* `back`   -- walk back to the first gap;
* `place`  -- rebuild the source stack, bottom-up: having placed pebbles `0, …, i-1`, push a new
  pebble and walk right until the source annotation marks the index `i` at the current gap.  This
  is where the stack discipline is used: the stack of the source configuration can be reconstructed
  because it is built from the bottom;
* `sim`    -- simulate `M` step by step.  Before each step the automaton checks whether the current
  configuration is the target, in which case it answers `true`; it dies if `M` dies, if `M` halts,
  or if a pop would take the stack below the floor `ℓ`.

The simulation is exact because the encoding has one letter per gap of the input string, so the
gaps of the encoded string that the automaton uses are literally the gaps of `w`, and the view of
`w` from a stack of pebbles is read off the view of the encoding by `PebEnc.unview`.  The only
mismatch is at the right end: the encoding is one letter longer than `w`, so a rightward move out of
the last gap of `w`, which kills `M`, has to be intercepted; the letter of the last gap is the
unique one whose input letter is absent, so this is a local test.
-/
import Lax194892Proofs.Source.PartD.PebEnc
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebReach

open PebEnc

variable {A B Q : Type} {k : ℕ}

/-! ## The state space -/

/-- The phase of the checking automaton. -/
inductive Phase (k : ℕ) : Type
  /-- Before the first pebble has been pushed. -/
  | start : Phase k
  /-- Walking to the right end, collecting the pebble indices that occur. -/
  | sweep : Phase k
  /-- Walking back to the first gap. -/
  | back : Phase k
  /-- Rebuilding the source stack; the pebble with index `i` is the one being placed. -/
  | place : Fin (k + 1) → Phase k
  /-- Simulating the pebble transducer. -/
  | sim : Phase k
  /-- The run has died. -/
  | dead : Phase k

/-- The state of the checking automaton. -/
structure RSt (Q : Type) (k : ℕ) where
  /-- The phase. -/
  phase : Phase k
  /-- The pebble indices seen in the source annotation. -/
  S : Fin k → Bool
  /-- The pebble indices seen in the target annotation. -/
  T : Fin k → Bool
  /-- The simulated state of the pebble transducer. -/
  q : Q

private def phaseOfCode (k : ℕ) (c : Fin 6 × Fin (k + 1)) : Phase k :=
  match c.1.val with
  | 0 => Phase.start
  | 1 => Phase.sweep
  | 2 => Phase.back
  | 3 => Phase.place c.2
  | 4 => Phase.sim
  | _ => Phase.dead

instance : Finite (Phase k) := by
  refine Finite.of_surjective (phaseOfCode k) ?_
  rintro (_ | _ | _ | i | _ | _)
  · exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), rfl⟩
  · exact ⟨(⟨1, by omega⟩, ⟨0, by omega⟩), rfl⟩
  · exact ⟨(⟨2, by omega⟩, ⟨0, by omega⟩), rfl⟩
  · exact ⟨(⟨3, by omega⟩, i), rfl⟩
  · exact ⟨(⟨4, by omega⟩, ⟨0, by omega⟩), rfl⟩
  · exact ⟨(⟨5, by omega⟩, ⟨0, by omega⟩), rfl⟩

instance [Finite Q] : Finite (RSt Q k) :=
  Finite.of_injective (fun s : RSt Q k => (s.phase, s.S, s.T, s.q))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; simp_all)

/-! ## Reading the view -/

/-- The value of a Boolean family of pebble indices at an arbitrary natural number. -/
def bidx (S : Fin k → Bool) (i : ℕ) : Bool := if h : i < k then S ⟨i, h⟩ else false

/-- The letter to the right of the head. -/
def rightLet {Γ : Type} (v : PebbleView Γ) : Option Γ := (v.getLast?).bind fun e => e.1.2

/-- The letter to the left of the head. -/
def leftLet {Γ : Type} (v : PebbleView Γ) : Option Γ := (v.getLast?).bind fun e => e.1.1

/-- The letter to the right of the `j`-th pebble. -/
def entryRight {Γ : Type} (v : PebbleView Γ) (j : ℕ) : Option Γ := (v[j]?).bind fun e => e.1.2

/-- The current configuration is the target one: every pebble `j` sits in a gap that the target
annotation marks with the index `j`, and the target annotation uses no index beyond the height of
the stack. -/
def tOk (T : Fin k → Bool) (v : PebbleView (PairLetter A Q k)) : Bool :=
  ((List.range v.length).all fun j =>
      match entryRight v j with
      | none => false
      | some c => bidx c.2.2.2.2 j) &&
    (List.finRange k).all fun i => if (i : ℕ) < v.length then true else !T i

/-- The successor of a pebble index, capped so that it stays in range. -/
def succIdx (i : Fin (k + 1)) : Fin (k + 1) := ⟨min ((i : ℕ) + 1) k, by omega⟩

/-! ## The automaton -/

open scoped Classical in
/-- The transition function of the checking automaton. -/
noncomputable def rstep (M : Pebble A B Q k) (ℓ : ℕ) (q₁ q₂ : Q)
    (s : RSt Q k) (v : PebbleView (PairLetter A Q k)) : RSt Q k × PebAutAction Bool :=
  match s.phase with
  | Phase.start =>
      ({ phase := Phase.sweep, S := fun _ => false, T := fun _ => false, q := q₁ },
        PebAutAction.push)
  | Phase.sweep =>
      match rightLet v with
      | none => ({ s with phase := Phase.back }, PebAutAction.move false)
      | some c =>
          ({ s with S := fun i => s.S i || c.2.2.2.1 i, T := fun i => s.T i || c.2.2.2.2 i },
            PebAutAction.move true)
  | Phase.back =>
      match leftLet v with
      | some _ => (s, PebAutAction.move false)
      | none =>
          if bidx s.S 0 then ({ s with phase := Phase.place ⟨0, by omega⟩ }, PebAutAction.stay)
          else ({ s with phase := Phase.sim, q := q₁ }, PebAutAction.pop)
  | Phase.place i =>
      match rightLet v with
      | none => ({ s with phase := Phase.dead }, PebAutAction.stay)
      | some c =>
          if bidx c.2.2.2.1 (i : ℕ) then
            if bidx s.S ((i : ℕ) + 1) then
              ({ s with phase := Phase.place (succIdx i) }, PebAutAction.push)
            else ({ s with phase := Phase.sim, q := q₁ }, PebAutAction.stay)
          else (s, PebAutAction.move true)
  | Phase.sim =>
      if tOk s.T v && decide (s.q = q₂) then (s, PebAutAction.halt true)
      else
        match (M.step s.q (unview v)).2 with
        | PebbleAction.out _ => ({ s with q := (M.step s.q (unview v)).1 }, PebAutAction.stay)
        | PebbleAction.terminate => ({ s with phase := Phase.dead }, PebAutAction.stay)
        | PebbleAction.push =>
            if v.length < k then ({ s with q := (M.step s.q (unview v)).1 }, PebAutAction.push)
            else ({ s with phase := Phase.dead }, PebAutAction.stay)
        | PebbleAction.pop =>
            if v.length = 0 ∨ v.length - 1 < ℓ then
              ({ s with phase := Phase.dead }, PebAutAction.stay)
            else ({ s with q := (M.step s.q (unview v)).1 }, PebAutAction.pop)
        | PebbleAction.move d =>
            if d then
              (match rightLet v with
                | some (_, _, some _, _, _) =>
                    ({ s with q := (M.step s.q (unview v)).1 }, PebAutAction.move true)
                | _ => ({ s with phase := Phase.dead }, PebAutAction.stay))
            else ({ s with q := (M.step s.q (unview v)).1 }, PebAutAction.move false)
  | Phase.dead => (s, PebAutAction.stay)

open scoped Classical in
/-- **The checking automaton.**  It has one pebble more than `M`, which is used by the phases that
inspect the annotation before the simulation starts. -/
noncomputable def reachAut (M : Pebble A B Q k) (ℓ : ℕ) (q₁ q₂ : Q) :
    PebbleAut (PairLetter A Q k) (RSt Q k) Bool (k + 1) where
  step := rstep M ℓ q₁ q₂

/-- The initial state. -/
def startSt (q₁ : Q) : RSt Q k :=
  { phase := Phase.start, S := fun _ => false, T := fun _ => false, q := q₁ }

/-- The state in which the simulation of `M` is carried out. -/
def simSt (S T : Fin k → Bool) (q : Q) : RSt Q k :=
  { phase := Phase.sim, S := S, T := T, q := q }

/-- The indices of a stack, as a Boolean family. -/
def hmark (k : ℕ) (st : List ℕ) : Fin k → Bool := fun i => decide ((i : ℕ) < st.length)

end PebReach

end Lax194892Proofs.Transducers
