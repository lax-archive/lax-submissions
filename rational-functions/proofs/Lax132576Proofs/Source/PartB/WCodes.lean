/- Finite descriptions (codes) of weighted automata over the field of rationals, used in the
decidability statements of Section *Rational relations and weighted automata* of *Transducers* (M.
Bojańczyk).

These definitions were moved here from `RequestProject/PartB/WeightedStatements.lean`, so that the
decision procedures of Theorems `thm:equivalence-weighted-automata`,
`thm:equivalence-rational-functions` and `thm:zeroness-weighted-automata` can be developed before
the statements of the numbered results.  The file also contains the basic facts about codes that
those procedures need: a coded automaton reads only the finitely many letters occurring in its
transitions, so it computes the value `0` on every string that uses another letter. -/
import Lax132576Proofs.Source.PartB.Codes
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

open LabAut

/-- A finite description of a weighted automaton over `ℚ` with states and
input letters coded by natural numbers.  A transition `(p, u, (a, b), q)` goes
from the state `p` to the state `q`, reads the string `u` and has the weight
`a / b`. -/
abbrev WCode := List (ℕ × List ℕ × (ℤ × ℕ) × ℕ) × List ℕ × List ℕ

/-- The weighted automaton described by a code. -/
def wcodeAut (c : WCode) : LabAut ℕ ℚ ℕ where
  init := {q | q ∈ c.2.1}
  final := {q | q ∈ c.2.2}
  δ := {t | ∃ s ∈ c.1, t = (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)}
  δ_finite := Set.Finite.ofFinset
    (c.1.toFinset.image (fun s => (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)))
    (by intro t; simp [eq_comm])

/-- The function computed by the weighted automaton described by a code. -/
noncomputable def wcodeEval (c : WCode) : List ℕ → ℚ := (wcodeAut c).wEval

/-- The promise that a code describes a genuine weighted automaton, i.e. that
every input string has finitely many accepting runs. -/
def WCodeValid (c : WCode) : Prop := (wcodeAut c).FinitelyManyRuns

/-! ## The alphabet of a coded weighted automaton -/

/-- The letters that the weighted automaton described by a code can read: those
occurring in the input strings of its transitions. -/
def wcodeAlphabet (c : WCode) : List ℕ := c.1.flatMap (fun t => t.2.1)

lemma wcode_mem_alphabet_of_mem_input {c : WCode}
    {ts : List (ℕ × List ℕ × ℚ × ℕ)} (hts : ∀ t ∈ ts, t ∈ (wcodeAut c).δ)
    {x : ℕ} (hx : x ∈ inputOf ts) : x ∈ wcodeAlphabet c := by
  simp only [inputOf, List.mem_flatten, List.mem_map] at hx
  obtain ⟨u, ⟨t, ht, rfl⟩, hxu⟩ := hx
  obtain ⟨s, hs, hst⟩ := hts t ht
  refine List.mem_flatMap.2 ⟨s, hs, ?_⟩
  subst hst
  exact hxu

/-- A coded weighted automaton has no accepting run over a string using a letter
that does not occur in its transitions. -/
lemma acceptingOn_eq_empty_of_foreign {c : WCode} {v : List ℕ} {x : ℕ} (hxv : x ∈ v)
    (hx : x ∉ wcodeAlphabet c) : (wcodeAut c).acceptingOn v = ∅ := by
  ext ts
  simp only [Set.mem_empty_iff_false, iff_false, LabAut.acceptingOn, Set.mem_setOf_eq, not_and]
  rintro ⟨q, -, p, -, hpath⟩ hin
  exact hx (wcode_mem_alphabet_of_mem_input (fun t ht => Path.mem_delta hpath t ht)
    (by rw [hin]; exact hxv))

/-- The value of a coded weighted automaton on a string that uses a letter not
occurring in its transitions is `0`. -/
lemma wcodeEval_eq_zero_of_foreign {c : WCode} {v : List ℕ} {x : ℕ} (hxv : x ∈ v)
    (hx : x ∉ wcodeAlphabet c) : wcodeEval c v = 0 := by
  show (wcodeAut c).wEval v = 0
  rw [LabAut.wEval, acceptingOn_eq_empty_of_foreign hxv hx, finsum_mem_empty]

/-! ## The zero code -/

/-- The code of the weighted automaton with no state and no transition; it
computes the constant function `0`. -/
def zeroWCode : WCode := ([], [], [])

lemma wcodeEval_zeroWCode : wcodeEval zeroWCode = 0 := by
  funext v
  show (wcodeAut zeroWCode).wEval v = 0
  have : (wcodeAut zeroWCode).acceptingOn v = ∅ := by
    ext ts
    simp only [Set.mem_empty_iff_false, iff_false, LabAut.acceptingOn, Set.mem_setOf_eq, not_and]
    rintro ⟨q, hq, -⟩
    exact absurd hq (by simp [wcodeAut, zeroWCode])
  rw [LabAut.wEval, this, finsum_mem_empty]

lemma wCodeValid_zeroWCode : WCodeValid zeroWCode := by
  intro v
  have : (wcodeAut zeroWCode).acceptingOn v = ∅ := by
    ext ts
    simp only [Set.mem_empty_iff_false, iff_false, LabAut.acceptingOn, Set.mem_setOf_eq, not_and]
    rintro ⟨q, hq, -⟩
    exact absurd hq (by simp [wcodeAut, zeroWCode])
  rw [this]
  exact Set.finite_empty

end Lax132576Proofs.Transducers
