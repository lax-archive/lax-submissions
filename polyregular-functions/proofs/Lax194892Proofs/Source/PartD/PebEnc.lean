/-
**The string representation of a configuration of a pebble transducer.**

Section D.2 of *Transducers* (M. Bojańczyk) carries out several proofs by encoding configurations,
and graphs of configurations, of a pebble transducer as strings over a finite alphabet, exactly as
Section C.2 does for two-way transducers.  This file introduces that encoding.

For a pebble transducer with states `Q` and at most `k` pebbles, a configuration on an input string
`w` of length `n` consists of a state and a stack of at most `k` *gaps* of `w`, that is, of elements
of `{0, …, n}`.  The book writes the string representation of such a configuration as an element of

  `Q · (A ∪ {x₁, …, x_ℓ})*`,

with the marker `x_i` inserted at the gap where pebble `i` sits.  The rendering used here carries
exactly the same information, in the shape that the book itself asks for when it represents a graph
of configurations -- *"a string over a fixed finite alphabet, whose length is the same as the input
string"*: the string has **one letter per gap** of `w`, the letter for the gap `p` consisting of

* the state (repeated in every letter, in place of the book's leading `Q`),
* the letter `w[p]`, which is present for `p < n` and absent for the last gap `p = n`, and
* the set of pebbles that sit in the gap `p`.

Since a configuration has to be able to speak about the last gap, the string is one letter longer
than the input; the extra letter, the only one whose `Option A` component is `none`, marks the end.
The book's reading order of consecutive pebble markers ("listed in increasing order") is not needed
here, because the markers of a gap are recorded as a *set* `Fin k → Bool`.

The results of Section D.2 speak about *two* configurations at a time -- a source and a target, in
Lemma `lem:reachability-pebble-automaton` -- so the alphabet defined here, `PebEnc.PairLetter`,
carries two states and two pebble annotations; `PebEnc.pairEnc` is the string representation of a
pair of configurations of a common input string.

The file also defines `Transducers.Pebble.RestrReaches`, reachability along runs which never pop
below a fixed stack height; with the height `0` it is ordinary reachability, and with the height `ℓ`
it is the book's notion of a *balanced run* of Claim `claim:reachability-basic-run`.
-/
import Lax194892Proofs.Source.PartD.PebbleReg
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace Pebble

variable {A B Q : Type} {k : ℕ}

/-- **Reachability along runs of stack height at least `ℓ`.**  Every configuration of the run,
including its endpoints, is required to be a proper configuration whose stack has height at least
`ℓ`; in particular the topmost `ℓ` pebbles are never popped.

For `ℓ = 0` this is ordinary reachability between two configurations
(`Pebble.restrReaches_zero_iff`).  For a run whose endpoints have height exactly `ℓ` it is the
book's notion of a *balanced run*: the source and the target have the same height and the pebble at
height `ℓ` -- the head -- is never popped, although it may be moved. -/
inductive RestrReaches (M : Pebble A B Q k) (w : List A) (ℓ : ℕ) :
    PebbleCfg Q → PebbleCfg Q → Prop
  /-- The empty run. -/
  | refl (q : Q) (st : List ℕ) (h : ℓ ≤ st.length) :
      RestrReaches M w ℓ (PebbleCfg.conf q st) (PebbleCfg.conf q st)
  /-- One step, from a configuration of height at least `ℓ`. -/
  | step {q : Q} {st : List ℕ} {c' c'' : PebbleCfg Q} {o : List B} (h : ℓ ≤ st.length)
      (hs : M.stepCfg w (PebbleCfg.conf q st) = some (o, c'))
      (hr : RestrReaches M w ℓ c' c'') :
      RestrReaches M w ℓ (PebbleCfg.conf q st) c''

/-- **A balanced run** in the sense of the book: a run between two configurations of height `ℓ`
during which the pebble at height `ℓ` is never popped. -/
def BalancedRun (M : Pebble A B Q k) (w : List A) (ℓ : ℕ) (c c' : PebbleCfg Q) : Prop :=
  M.RestrReaches w ℓ c c'

variable {M : Pebble A B Q k} {w : List A}

/-- Nothing happens after the run has halted. -/
lemma reaches_halt_eq {v : List B} {c : PebbleCfg Q} (h : M.Reaches w PebbleCfg.halt v c) :
    c = PebbleCfg.halt := by
  cases h with
  | refl _ => rfl
  | step hs _ => exact absurd hs (by simp [Pebble.stepCfg])

lemma restrReaches_zero_of_reaches :
    ∀ {c c'' : PebbleCfg Q} {v : List B}, M.Reaches w c v c'' →
      ∀ {q st}, c = PebbleCfg.conf q st → (∃ q' st', c'' = PebbleCfg.conf q' st') →
        M.RestrReaches w 0 c c'' := by
  intro c c'' v h
  induction h with
  | refl c =>
      rintro q st rfl -
      exact RestrReaches.refl _ _ (Nat.zero_le _)
  | @step c c' c'' o o' hs hr ih =>
      rintro q st rfl hend
      cases hc' : c' with
      | halt =>
          obtain ⟨q', st', hq'⟩ := hend
          rw [hc'] at hr
          rw [reaches_halt_eq hr] at hq'
          exact absurd hq' (by simp)
      | conf q'' st'' =>
          exact RestrReaches.step (Nat.zero_le _) hs (ih (by rw [hc']) hend)

lemma reaches_of_restrReaches {ℓ : ℕ} {c c'' : PebbleCfg Q} (h : M.RestrReaches w ℓ c c'') :
    ∃ v, M.Reaches w c v c'' := by
  induction h with
  | refl q st _ => exact ⟨[], Reaches.refl _⟩
  | step _ hs _ ih => obtain ⟨v, hv⟩ := ih; exact ⟨_, Reaches.step hs hv⟩

/-- Reachability along runs of height at least `0` is ordinary reachability. -/
lemma restrReaches_zero_iff {q st q' st'} :
    M.RestrReaches w 0 (PebbleCfg.conf q st) (PebbleCfg.conf q' st') ↔
      ∃ v, M.Reaches w (PebbleCfg.conf q st) v (PebbleCfg.conf q' st') := by
  refine ⟨reaches_of_restrReaches, ?_⟩
  rintro ⟨v, hv⟩
  exact restrReaches_zero_of_reaches hv rfl ⟨q', st', rfl⟩

end Pebble

namespace PebEnc

variable {A B Q : Type} {k : ℕ}

/-- The set of pebbles of the stack `st` that sit in the gap `p`. -/
def ann (k : ℕ) (st : List ℕ) (p : ℕ) : Fin k → Bool := fun i => decide (st[(i : ℕ)]? = some p)

/-- **The alphabet of the string representation of a pair of configurations.**  A letter describes
one gap of the input string: the two states, the input letter that follows the gap (absent for the
last gap) and, for the source and for the target configuration, the set of pebbles sitting in the
gap. -/
abbrev PairLetter (A Q : Type) (k : ℕ) := Q × Q × Option A × (Fin k → Bool) × (Fin k → Bool)

/-- **The string representation of a pair of configurations** `(q₁, sts)` and `(q₂, stt)` of the
input string `w`: one letter per gap of `w`. -/
def pairEnc (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A) : List (PairLetter A Q k) :=
  (List.range (w.length + 1)).map fun p => (q₁, q₂, w[p]?, ann k sts p, ann k stt p)

variable (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A)

@[simp] lemma pairEnc_length : (pairEnc (k := k) q₁ q₂ sts stt w).length = w.length + 1 := by
  simp [pairEnc]

lemma pairEnc_getElem? {p : ℕ} (hp : p ≤ w.length) :
    (pairEnc (k := k) q₁ q₂ sts stt w)[p]? =
      some (q₁, q₂, w[p]?, ann k sts p, ann k stt p) := by
  have hlt : p < (List.range (w.length + 1)).length := by simp; omega
  rw [pairEnc, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

lemma pairEnc_getElem?_of_gt {p : ℕ} (hp : w.length < p) :
    (pairEnc (k := k) q₁ q₂ sts stt w)[p]? = none := by
  rw [List.getElem?_eq_none]
  simp only [pairEnc_length]
  omega

lemma pairEnc_ne_nil : pairEnc (k := k) q₁ q₂ sts stt w ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this

/-! ## Translating the view of the encoded input back to the view of the input -/

/-- The pair of input letters adjacent to a gap, read off the pair of letters of the encoding that
are adjacent to it. -/
def unviewPair : Option (PairLetter A Q k) × Option (PairLetter A Q k) → Option A × Option A :=
  fun c => (c.1.bind (fun x => x.2.2.1), c.2.bind (fun x => x.2.2.1))

/-- The view of the input string, read off the view of its encoding. -/
def unview (v : PebbleView (PairLetter A Q k)) : PebbleView A :=
  v.map fun e => (unviewPair e.1, e.2)

lemma unview_viewOf (st : List ℕ) (hst : ∀ p ∈ st, p ≤ w.length) :
    unview (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st) = viewOf w st := by
  simp only [unview, viewOf, List.map_map]
  refine List.map_congr_left ?_
  intro p hp
  have hple : p ≤ w.length := hst p hp
  simp only [Function.comp_apply, unviewPair, Prod.mk.injEq, and_true]
  constructor
  · by_cases hp0 : p = 0
    · simp [hp0]
    · simp only [hp0, if_false]
      rw [pairEnc_getElem? q₁ q₂ sts stt w (by omega)]
      rfl
  · rw [pairEnc_getElem? q₁ q₂ sts stt w hple]
    rfl

end PebEnc

end Lax194892Proofs.Transducers
