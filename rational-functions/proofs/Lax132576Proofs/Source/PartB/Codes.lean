/-
Finite descriptions (codes) of nondeterministic automata with output, and the
formalisation of decidability statements used in Part B of *Transducers*
(M. Bojańczyk).

These definitions were moved here from `RequestProject/PartB/RationalStatements.lean` so that the
reduction proving Theorem `thm:undecidable-equivalence-rational-relations` (in
`RequestProject/PartB/PCPRed.lean`) can be developed before the statements of the numbered results.
-/
import Lax132576Proofs.Source.PartB.PathComb
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-- A finite description of a nondeterministic automaton with output whose
states are natural numbers and whose input and output alphabets are `ℕ`. -/
abbrev RelCode := List (ℕ × List ℕ × List ℕ × ℕ) × List ℕ × List ℕ

/-- The automaton described by a code. -/
def codeAut (c : RelCode) : NFAO ℕ ℕ ℕ where
  init := {q | q ∈ c.2.1}
  final := {q | q ∈ c.2.2}
  δ := {t | t ∈ c.1}
  δ_finite := c.1.finite_toSet

/-- The rational relation described by a code. -/
def codeRel (c : RelCode) : List ℕ → List ℕ → Prop := (codeAut c).rel

/-- The letters that the automaton described by a code can read: those occurring
in the input strings of its transitions. -/
def codeAlphabet (c : RelCode) : List ℕ := c.1.flatMap (fun t => t.2.1)

/-- A string over the alphabet of a code. -/
def CodeWord (c : RelCode) (w : List ℕ) : Prop := ∀ x ∈ w, x ∈ codeAlphabet c

/-  The predicate originally used to say that the relation described by a code
is a total function was

  `def CodeFunctional (c : RelCode) : Prop := ∀ w, ∃! v, codeRel c w v`,

that is, totality on *all* of `ℕ*`.  This is never satisfied
(`not_codeTotalFunctional` below), because a code has only finitely many
transitions and hence reads only finitely many letters, so it would have made
every statement with that promise vacuous.  It is kept below under the name
`CodeTotalFunctional`, and the promise used in the decidability statements is
now totality on strings over the alphabet of the code. -/

/-- Totality of the relation described by a code on *all* of `ℕ*`.  This is
never satisfied; see `not_codeTotalFunctional`. -/
def CodeTotalFunctional (c : RelCode) : Prop := ∀ w, ∃! v, codeRel c w v

lemma le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      rcases List.mem_cons.1 h with rfl | h'
      · simp
      · exact le_trans (ih h') (by simp)

lemma mem_codeAlphabet_of_mem_input {c : RelCode} {ts : List (ℕ × List ℕ × List ℕ × ℕ)}
    (hts : ∀ t ∈ ts, t ∈ c.1) {x : ℕ} (hx : x ∈ LabAut.inputOf ts) : x ∈ codeAlphabet c := by
  simp only [LabAut.inputOf, List.mem_flatten, List.mem_map] at hx
  obtain ⟨u, ⟨t, ht, rfl⟩, hxu⟩ := hx
  exact List.mem_flatMap.2 ⟨t, hts t ht, hxu⟩

/-- A code can only read finitely many letters, so the relation that it
describes is never a total function on all of `ℕ*`. -/
theorem not_codeTotalFunctional (c : RelCode) : ¬ CodeTotalFunctional c := by
  intro h
  set N := (codeAlphabet c).foldr max 0 + 1 with hN
  obtain ⟨v, hv, -⟩ := h [N]
  obtain ⟨ts, ⟨q, -, p, -, hpath⟩, hin, -⟩ := hv
  have hts : ∀ t ∈ ts, t ∈ c.1 := fun t ht => LabAut.Path.mem_delta hpath t ht
  have hmem : N ∈ LabAut.inputOf ts := by rw [hin]; simp
  have := le_foldr_max (mem_codeAlphabet_of_mem_input hts hmem)
  omega

/-- The predicate saying that the relation described by a code is a total
function on strings over the alphabet of the code. -/
def CodeFunctional (c : RelCode) : Prop := ∀ w, CodeWord c w → ∃! v, codeRel c w v

/-- A predicate `P` is decidable under a promise if there is a computable
`Bool`-valued function that answers `P` correctly on all inputs satisfying the
promise. -/
def DecidableUnderPromise {α : Type} [Primcodable α] (promise P : α → Prop) : Prop :=
  ∃ D : α → Bool, Computable D ∧ ∀ a, promise a → (D a = true ↔ P a)

end Lax132576Proofs.Transducers
