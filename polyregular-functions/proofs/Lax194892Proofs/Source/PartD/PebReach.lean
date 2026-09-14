/-
**Reachability between configurations of a pebble machine is a regular property of the string
representation of the pair of configurations.**

This file states and proves the two results of Section *Pebble transducers* of *Transducers*
(M. Bojańczyk) that are about the string representation of configurations:

* Lemma `lem:reachability-pebble-automaton` -- reachability between two configurations is
  definable, and
* Claim `claim:reachability-basic-run` -- the same for *balanced runs*, the runs between two
  configurations of the same height `ℓ` during which the pebble at height `ℓ` is never popped.

Two deliberate divergences from the book, both documented on the statements themselves.

* The book asks for an **mso formula** `φ(s, t)` with two free variables of the type of
  configurations.  Here the pair of configurations is instead *encoded into the input string*
  (`RequestProject/PartD/PebEnc.lean`) and the conclusion is that the set of encodings of
  reachable pairs is a **regular language**.  The two formulations are interchangeable: regular
  languages are exactly the mso-definable ones by Theorem `thm:mso-logic-languages`
  (`Transducers.regular_iff_msoDefinable`), and an mso formula with free variables is evaluated on
  an annotated string exactly as here, by Lemma `lem:mso-free-variables`
  (`Transducers.mso_annotated_regular`).  What is *not* produced is a formula literally of the
  book's shape; the free variables are carried by the letters instead.
* An mso formula is only ever evaluated on a genuine structure, so the language is only required to
  be correct on genuine encodings: the hypotheses of the statements below say that the two stacks
  are stacks of at most `k` pebbles of the input string.  On strings that encode nothing the
  automaton may answer anything.

The mathematical content is `PebReach.reachAut_answers_iff`
(`RequestProject/PartD/PebReachSim.lean`), the correctness of the checking pebble automaton of
`RequestProject/PartD/PebReachAut.lean`; here it is only combined with
`Transducers.pebbleAut_answers_isRegular` (pebble automata recognise regular languages) and with
the closure properties of regular languages, to produce **one** language for all pairs of states,
as the book's single formula `φ(s, t)` has the state as a part of its two free variables.
-/
import Lax194892Proofs.Source.PartD.PebReachSim
import Lax194892Proofs.Source.PartD.PebbleLev1
import Lax916827Proofs.Source.PartC.RegAut
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebEnc

open PebReach

variable {A B Q : Type} {k : ℕ}

open scoped Classical in
/-- The language of encodings of a pair of configurations `(q₁, sts)`, `(q₂, stt)` such that the
first reaches the second by a run that never pops below the floor `ℓ`.  The second conjunct pins
the two states down: the states are carried by every letter of the encoding. -/
noncomputable def reachLangAt (M : Pebble A B Q k) (ℓ : ℕ) (q₁ q₂ : Q) :
    Language (PairLetter A Q k) :=
  {u | (reachAut M ℓ q₁ q₂).Answers u (Sum.inl (startSt q₁, [])) true ∧
    ∀ c ∈ u, (decide (c.1 = q₁) && decide (c.2.1 = q₂)) = true}

/-- **The language of reachable pairs of configurations**, over all pairs of states. -/
noncomputable def reachLang (M : Pebble A B Q k) (ℓ : ℕ) : Language (PairLetter A Q k) :=
  {u | ∃ p : Q × Q, u ∈ reachLangAt M ℓ p.1 p.2}

variable [Finite A] [Finite Q]

lemma reachLangAt_isRegular (M : Pebble A B Q k) (ℓ : ℕ) (q₁ q₂ : Q) :
    (reachLangAt M ℓ q₁ q₂).IsRegular := by
  classical
  refine RegAut.isRegular_of_eq
    (RegAut.isRegular_and
      (pebbleAut_answers_isRegular (k + 1) (reachAut M ℓ q₁ q₂) (startSt q₁) true)
      (RegAut.isRegular_all (fun c : PairLetter A Q k =>
        decide (c.1 = q₁) && decide (c.2.1 = q₂)))) ?_
  intro u
  exact Iff.rfl

lemma reachLang_isRegular (M : Pebble A B Q k) (ℓ : ℕ) : (reachLang M ℓ).IsRegular :=
  RegAut.isRegular_exists_finite _ (fun p => reachLangAt_isRegular M ℓ p.1 p.2)

omit [Finite A] [Finite Q] in
/-- Membership of a genuine encoding in `PebEnc.reachLang`. -/
lemma mem_reachLang_iff (M : Pebble A B Q k) (ℓ : ℕ) (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A)
    (hstsb : ∀ p ∈ sts, p ≤ w.length) (hsttb : ∀ p ∈ stt, p ≤ w.length)
    (hstsk : sts.length ≤ k) (hsttk : stt.length ≤ k) (hl : ℓ ≤ sts.length) :
    pairEnc q₁ q₂ sts stt w ∈ reachLang M ℓ ↔
      M.RestrReaches w ℓ (PebbleCfg.conf q₁ sts) (PebbleCfg.conf q₂ stt) := by
  classical
  constructor
  · rintro ⟨⟨p₁, p₂⟩, hans, hlet⟩
    have hp : p₁ = q₁ ∧ p₂ = q₂ := by
      have hmem : (q₁, q₂, w[0]?, ann k sts 0, ann k stt 0) ∈ pairEnc q₁ q₂ sts stt w := by
        simp only [pairEnc, List.mem_map, List.mem_range]
        exact ⟨0, by omega, rfl⟩
      have := hlet _ hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1.symm, this.2.symm⟩
    obtain ⟨rfl, rfl⟩ := hp
    exact (reachAut_answers_iff M ℓ p₁ p₂ sts stt w hstsb hsttb hstsk hsttk hl).1 hans
  · intro h
    refine ⟨(q₁, q₂), (reachAut_answers_iff M ℓ q₁ q₂ sts stt w hstsb hsttb hstsk hsttk hl).2 h,
      ?_⟩
    intro c hc
    simp only [pairEnc, List.mem_map] at hc
    obtain ⟨p, -, rfl⟩ := hc
    simp

end PebEnc

/-! ## The two results of the book -/

open PebEnc

variable {A B Q : Type} {k : ℕ} [Finite A] [Finite Q]

/-- **Lemma `lem:reachability-pebble-automaton`.**  Reachability between two configurations of a
`k`-pebble machine is a regular property of the string representation of the pair of
configurations -- equivalently, by Theorem `thm:mso-logic-languages`, an mso-definable one.

The book states this for a pebble *automaton* and asks for an mso formula `φ(s, t)` whose two free
variables range over configurations.  Here the pair of configurations is encoded into the input
string by `PebEnc.pairEnc`, and the conclusion is regularity of the set of encodings; see the
header of this file.  The statement is given for the pebble *transducers* of
`RequestProject/PartD/PebbleDef.lean`; the configuration graph of a pebble automaton is the
configuration graph of a pebble transducer, and it is the transducer version that Section
*Equivalence with for-transducers* needs. -/
theorem reachability_pebble_automaton (M : Pebble A B Q k) :
    ∃ L : Language (PairLetter A Q k), L.IsRegular ∧
      ∀ (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A),
        (∀ p ∈ sts, p ≤ w.length) → (∀ p ∈ stt, p ≤ w.length) →
        sts.length ≤ k → stt.length ≤ k →
        (pairEnc q₁ q₂ sts stt w ∈ L ↔
          ∃ v, M.Reaches w (PebbleCfg.conf q₁ sts) v (PebbleCfg.conf q₂ stt)) := by
  refine ⟨reachLang M 0, reachLang_isRegular M 0, ?_⟩
  intro q₁ q₂ sts stt w hstsb hsttb hstsk hsttk
  rw [mem_reachLang_iff M 0 q₁ q₂ sts stt w hstsb hsttb hstsk hsttk (Nat.zero_le _)]
  exact Pebble.restrReaches_zero_iff

/-- **Claim `claim:reachability-basic-run`.**  For every height `ℓ ∈ {1, …, k}`, the existence of a
*balanced run* -- a run between two configurations of height `ℓ` during which the pebble at height
`ℓ` is never popped, although it may be moved -- is a regular property of the string representation
of the pair of configurations.

The book writes the two endpoints as `(x, y₁)` and `(x, y₂)`, where `x` is the common prefix of the
stack of height `ℓ - 1` and `yᵢ` is the pair consisting of the state and the position of the top
pebble; that is exactly the shape of the two stacks below.  As in Lemma
`lem:reachability-pebble-automaton` the mso formula of the book is replaced by a regular language
of encodings. -/
theorem reachability_basic_run (M : Pebble A B Q k) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    ∃ L : Language (PairLetter A Q k), L.IsRegular ∧
      ∀ (q₁ q₂ : Q) (x : List ℕ) (p₁ p₂ : ℕ) (w : List A),
        (∀ p ∈ x, p ≤ w.length) → p₁ ≤ w.length → p₂ ≤ w.length → x.length = ℓ - 1 →
        (pairEnc q₁ q₂ (x ++ [p₁]) (x ++ [p₂]) w ∈ L ↔
          M.BalancedRun w ℓ (PebbleCfg.conf q₁ (x ++ [p₁])) (PebbleCfg.conf q₂ (x ++ [p₂]))) := by
  refine ⟨reachLang M ℓ, reachLang_isRegular M ℓ, ?_⟩
  intro q₁ q₂ x p₁ p₂ w hxb hp₁ hp₂ hxl
  have hlen : (x ++ [p₁]).length = ℓ := by simp [hxl]; omega
  have hlen' : (x ++ [p₂]).length = ℓ := by simp [hxl]; omega
  refine mem_reachLang_iff M ℓ q₁ q₂ (x ++ [p₁]) (x ++ [p₂]) w ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hxb p hp
    · simp only [List.mem_singleton] at hp; omega
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hxb p hp
    · simp only [List.mem_singleton] at hp; omega
  · omega
  · omega
  · omega

end Lax194892Proofs.Transducers
