/-
Two constructions on codes used for Theorem `thm:decide-if-mealy` of *Transducers*
(M. Bojańczyk): deciding whether the function described by a code is prefix
preserving.

For a *length preserving* function `f` on the strings over the alphabet of the
code, prefix preservation is the identity

  `dropLast (f w) = f (dropLast w)`,

so it is an equality of two rational functions, and Theorem `thm:equivalence-rational-functions`
decides it. This file builds codes for the two sides.

* `dropCode c` computes `w ↦ dropLast (f w)`.  Its states are the states of `c`
  with a phase in `{0, 1, 2}`: the phase `2` means that the run has produced no
  output yet, the phase `0` that it has produced some output but the last letter
  of the output has not been dropped yet, and the phase `1` that it has been
  dropped.  The transition dropping the letter is the last one with a nonempty
  output; after it, only transitions with empty output may be used.  A run is
  accepting if it ends in the phase `1`, or in the phase `2` -- in which case
  the whole output is empty and equal to its own `dropLast`.
* `shiftCode c` computes `w ↦ f (dropLast w)`.  It is `c` with an extra
  transition from every final state, reading one letter and writing nothing,
  into a fresh final state, together with a second fresh state which is both
  initial and final and accounts for the empty input.
-/
import Lax132576Proofs.Source.PartB.CodeAlpha
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace PrefixCodes

open LabAut LenDec

/-- The type of coded transitions. -/
abbrev Tr := ℕ × List ℕ × List ℕ × ℕ

/-! ## The code computing `w ↦ dropLast (f w)` -/

/-- The transitions of `dropCode` coming from one transition of the code. -/
def dropTrans (t : Tr) : List Tr :=
  if t.2.2.1 = [] then
    [(3 * t.1 + 2, t.2.1, [], 3 * t.2.2.2 + 2), (3 * t.1, t.2.1, [], 3 * t.2.2.2),
      (3 * t.1 + 1, t.2.1, [], 3 * t.2.2.2 + 1)]
  else
    [(3 * t.1 + 2, t.2.1, t.2.2.1, 3 * t.2.2.2), (3 * t.1, t.2.1, t.2.2.1, 3 * t.2.2.2),
      (3 * t.1 + 2, t.2.1, t.2.2.1.dropLast, 3 * t.2.2.2 + 1),
      (3 * t.1, t.2.1, t.2.2.1.dropLast, 3 * t.2.2.2 + 1)]

/-- The code computing `w ↦ dropLast (f w)`. -/
def dropCode (c : RelCode) : RelCode :=
  (c.1.flatMap dropTrans, c.2.1.map (fun q => 3 * q + 2),
    c.2.2.flatMap (fun p => [3 * p + 2, 3 * p + 1]))

/-! ### The transitions of `dropCode` -/

/-- The transitions of `dropCode c` are those produced by `dropTrans` from the
transitions of `c`. -/
lemma mem_dropCode {c : RelCode} {t' : Tr} :
    t' ∈ (dropCode c).1 ↔ ∃ t ∈ c.1, t' ∈ dropTrans t := by
  simp [dropCode, List.mem_flatMap]

/-! ### Soundness: a run of `dropCode c` projects to a run of `c` -/

/-- From a state of the phase `1` only transitions writing nothing are
available, so the run has empty output and projects to a run of `c` with empty
output. -/
lemma drop_sound_one (c : RelCode) : ∀ (ts' : List Tr) (q P : ℕ),
    (codeAut (dropCode c)).Path (3 * q + 1) ts' P →
    ∃ (p : ℕ) (ts : List Tr), P = 3 * p + 1 ∧ (codeAut c).Path q ts p ∧
      inputOf ts = inputOf ts' ∧ NFAO.outputOf ts = [] ∧ NFAO.outputOf ts' = [] := by
  intro ts'
  induction ts' with
  | nil =>
      intro q P h
      exact ⟨q, [], (Path.eq_of_nil h).symm, Path.nil q, rfl, rfl, rfl⟩
  | cons t' ts'' ih =>
      intro q P h
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv h
      obtain ⟨t, ht, hin⟩ := mem_dropCode.1 hmem
      obtain ⟨p₀, a, x, p₁⟩ := t
      by_cases hx : x = []
      · subst hx
        simp [dropTrans] at hin
        rcases hin with rfl | rfl | rfl
        · exact absurd (show 3 * p₀ + 2 = 3 * q + 1 from hsrc) (by omega)
        · exact absurd (show 3 * p₀ = 3 * q + 1 from hsrc) (by omega)
        · have hq : p₀ = q := by
            have : 3 * p₀ + 1 = 3 * q + 1 := hsrc
            omega
          subst hq
          obtain ⟨p, ts, hP, hpath, hinp, hout, hout'⟩ := ih p₁ P hrest
          exact ⟨p, (p₀, a, [], p₁) :: ts, hP, Path.cons ht hpath, by simp [hinp],
            by simp [hout], by simp [hout']⟩
      · simp [dropTrans, hx] at hin
        rcases hin with rfl | rfl | rfl | rfl
        · exact absurd (show 3 * p₀ + 2 = 3 * q + 1 from hsrc) (by omega)
        · exact absurd (show 3 * p₀ = 3 * q + 1 from hsrc) (by omega)
        · exact absurd (show 3 * p₀ + 2 = 3 * q + 1 from hsrc) (by omega)
        · exact absurd (show 3 * p₀ = 3 * q + 1 from hsrc) (by omega)

/-- From a state of the phase `0` the run either stays in the phase `0`, and
then it has the same output as the run of `c` it projects to, or it drops the
last letter of that output. -/
lemma drop_sound_zero (c : RelCode) : ∀ (ts' : List Tr) (q P : ℕ),
    (codeAut (dropCode c)).Path (3 * q) ts' P →
    ∃ (p : ℕ) (ts : List Tr), (codeAut c).Path q ts p ∧ inputOf ts = inputOf ts' ∧
      ((P = 3 * p ∧ NFAO.outputOf ts' = NFAO.outputOf ts) ∨
        (P = 3 * p + 1 ∧ NFAO.outputOf ts ≠ [] ∧
          NFAO.outputOf ts' = (NFAO.outputOf ts).dropLast)) := by
  intro ts'
  induction ts' with
  | nil =>
      intro q P h
      exact ⟨q, [], Path.nil q, rfl, Or.inl ⟨(Path.eq_of_nil h).symm, rfl⟩⟩
  | cons t' ts'' ih =>
      intro q P h
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv h
      obtain ⟨t, ht, hin⟩ := mem_dropCode.1 hmem
      obtain ⟨p₀, a, x, p₁⟩ := t
      by_cases hx : x = []
      · subst hx
        simp [dropTrans] at hin
        rcases hin with rfl | rfl | rfl
        · exact absurd (show 3 * p₀ + 2 = 3 * q from hsrc) (by omega)
        · have hq : p₀ = q := by
            have : 3 * p₀ = 3 * q := hsrc
            omega
          subst hq
          obtain ⟨p, ts, hpath, hinp, hcase⟩ := ih p₁ P hrest
          refine ⟨p, (p₀, a, [], p₁) :: ts, Path.cons ht hpath, by simp [hinp], ?_⟩
          rcases hcase with ⟨hP, hout⟩ | ⟨hP, hne, hout⟩
          · exact Or.inl ⟨hP, by simp [hout]⟩
          · exact Or.inr ⟨hP, by simpa using hne, by simp [hout]⟩
        · exact absurd (show 3 * p₀ + 1 = 3 * q from hsrc) (by omega)
      · simp [dropTrans, hx] at hin
        rcases hin with rfl | rfl | rfl | rfl
        · exact absurd (show 3 * p₀ + 2 = 3 * q from hsrc) (by omega)
        · have hq : p₀ = q := by
            have : 3 * p₀ = 3 * q := hsrc
            omega
          subst hq
          obtain ⟨p, ts, hpath, hinp, hcase⟩ := ih p₁ P hrest
          refine ⟨p, (p₀, a, x, p₁) :: ts, Path.cons ht hpath, by simp [hinp], ?_⟩
          rcases hcase with ⟨hP, hout⟩ | ⟨hP, hne, hout⟩
          · exact Or.inl ⟨hP, by simp [hout]⟩
          · refine Or.inr ⟨hP, by simp [hne], ?_⟩
            simp only [NFAO.outputOf_cons, hout]
            rw [List.dropLast_append_of_ne_nil hne]
        · exact absurd (show 3 * p₀ + 2 = 3 * q from hsrc) (by omega)
        · have hq : p₀ = q := by
            have : 3 * p₀ = 3 * q := hsrc
            omega
          subst hq
          obtain ⟨p, ts, hP, hpath, hinp, hout, hout'⟩ := drop_sound_one c ts'' p₁ P hrest
          refine ⟨p, (p₀, a, x, p₁) :: ts, Path.cons ht hpath, by simp [hinp], ?_⟩
          refine Or.inr ⟨hP, by simp [hout, hx], ?_⟩
          simp [hout, hout']

/-- From a state of the phase `2` the run has produced no output while it stays
in the phase `2`. -/
lemma drop_sound_two (c : RelCode) : ∀ (ts' : List Tr) (q P : ℕ),
    (codeAut (dropCode c)).Path (3 * q + 2) ts' P →
    ∃ (p : ℕ) (ts : List Tr), (codeAut c).Path q ts p ∧ inputOf ts = inputOf ts' ∧
      ((P = 3 * p + 2 ∧ NFAO.outputOf ts = [] ∧ NFAO.outputOf ts' = []) ∨
        (P = 3 * p ∧ NFAO.outputOf ts' = NFAO.outputOf ts) ∨
        (P = 3 * p + 1 ∧ NFAO.outputOf ts ≠ [] ∧
          NFAO.outputOf ts' = (NFAO.outputOf ts).dropLast)) := by
  intro ts'
  induction ts' with
  | nil =>
      intro q P h
      exact ⟨q, [], Path.nil q, rfl, Or.inl ⟨(Path.eq_of_nil h).symm, rfl, rfl⟩⟩
  | cons t' ts'' ih =>
      intro q P h
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv h
      obtain ⟨t, ht, hin⟩ := mem_dropCode.1 hmem
      obtain ⟨p₀, a, x, p₁⟩ := t
      by_cases hx : x = []
      · subst hx
        simp [dropTrans] at hin
        rcases hin with rfl | rfl | rfl
        · have hq : p₀ = q := by
            have : 3 * p₀ + 2 = 3 * q + 2 := hsrc
            omega
          subst hq
          obtain ⟨p, ts, hpath, hinp, hcase⟩ := ih p₁ P hrest
          refine ⟨p, (p₀, a, [], p₁) :: ts, Path.cons ht hpath, by simp [hinp], ?_⟩
          rcases hcase with ⟨hP, hout, hout'⟩ | ⟨hP, hout⟩ | ⟨hP, hne, hout⟩
          · exact Or.inl ⟨hP, by simp [hout], by simp [hout']⟩
          · exact Or.inr (Or.inl ⟨hP, by simp [hout]⟩)
          · exact Or.inr (Or.inr ⟨hP, by simpa using hne, by simp [hout]⟩)
        · exact absurd (show 3 * p₀ = 3 * q + 2 from hsrc) (by omega)
        · exact absurd (show 3 * p₀ + 1 = 3 * q + 2 from hsrc) (by omega)
      · simp [dropTrans, hx] at hin
        rcases hin with rfl | rfl | rfl | rfl
        · have hq : p₀ = q := by
            have : 3 * p₀ + 2 = 3 * q + 2 := hsrc
            omega
          subst hq
          obtain ⟨p, ts, hpath, hinp, hcase⟩ := drop_sound_zero c ts'' p₁ P hrest
          refine ⟨p, (p₀, a, x, p₁) :: ts, Path.cons ht hpath, by simp [hinp], ?_⟩
          rcases hcase with ⟨hP, hout⟩ | ⟨hP, hne, hout⟩
          · exact Or.inr (Or.inl ⟨hP, by simp [hout]⟩)
          · refine Or.inr (Or.inr ⟨hP, by simp [hne], ?_⟩)
            simp only [NFAO.outputOf_cons, hout]
            rw [List.dropLast_append_of_ne_nil hne]
        · exact absurd (show 3 * p₀ = 3 * q + 2 from hsrc) (by omega)
        · have hq : p₀ = q := by
            have : 3 * p₀ + 2 = 3 * q + 2 := hsrc
            omega
          subst hq
          obtain ⟨p, ts, hP, hpath, hinp, hout, hout'⟩ := drop_sound_one c ts'' p₁ P hrest
          refine ⟨p, (p₀, a, x, p₁) :: ts, Path.cons ht hpath, by simp [hinp], ?_⟩
          refine Or.inr (Or.inr ⟨hP, by simp [hout, hx], ?_⟩)
          simp [hout, hout']
        · exact absurd (show 3 * p₀ = 3 * q + 2 from hsrc) (by omega)

/-! ### Completeness: a run of `c` is simulated by a run of `dropCode c` -/

/-- A run of `c` with empty output is simulated in the phase `1` and in the
phase `2`. -/
lemma drop_complete_empty (c : RelCode) : ∀ (ts : List Tr) (q p : ℕ),
    (codeAut c).Path q ts p → NFAO.outputOf ts = [] → ∀ φ, (φ = 1 ∨ φ = 2) →
    ∃ ts', (codeAut (dropCode c)).Path (3 * q + φ) ts' (3 * p + φ) ∧
      inputOf ts' = inputOf ts ∧ NFAO.outputOf ts' = [] := by
  intro ts
  induction ts with
  | nil =>
      intro q p hpath _ φ _
      exact ⟨[], (Path.eq_of_nil hpath) ▸ Path.nil _, rfl, rfl⟩
  | cons t ts'' ih =>
      intro q p hpath hout φ hφ
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv hpath
      obtain ⟨p₀, a, x, p₁⟩ := t
      have hsrc' : p₀ = q := hsrc
      subst hsrc'
      have hx : x = [] := by
        have := hout
        simp only [NFAO.outputOf_cons, List.append_eq_nil_iff] at this
        exact this.1
      subst hx
      have houtr : NFAO.outputOf ts'' = [] := by
        simpa using hout
      obtain ⟨ts', hpath', hin', hout'⟩ := ih p₁ p hrest houtr φ hφ
      refine ⟨(3 * p₀ + φ, a, [], 3 * p₁ + φ) :: ts', Path.cons ?_ hpath', by simp [hin'],
        by simp [hout']⟩
      refine mem_dropCode.2 ⟨(p₀, a, [], p₁), hmem, ?_⟩
      rcases hφ with rfl | rfl <;> simp [dropTrans]

/-- A run of `c` is simulated in the phase `0`, with the same output. -/
lemma drop_complete_keep (c : RelCode) : ∀ (ts : List Tr) (q p : ℕ),
    (codeAut c).Path q ts p →
    ∃ ts', (codeAut (dropCode c)).Path (3 * q) ts' (3 * p) ∧
      inputOf ts' = inputOf ts ∧ NFAO.outputOf ts' = NFAO.outputOf ts := by
  intro ts
  induction ts with
  | nil =>
      intro q p hpath
      exact ⟨[], (Path.eq_of_nil hpath) ▸ Path.nil _, rfl, rfl⟩
  | cons t ts'' ih =>
      intro q p hpath
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv hpath
      obtain ⟨p₀, a, x, p₁⟩ := t
      have hsrc' : p₀ = q := hsrc
      subst hsrc'
      obtain ⟨ts', hpath', hin', hout'⟩ := ih p₁ p hrest
      refine ⟨(3 * p₀, a, x, 3 * p₁) :: ts', Path.cons ?_ hpath', by simp [hin'],
        by simp [hout']⟩
      refine mem_dropCode.2 ⟨(p₀, a, x, p₁), hmem, ?_⟩
      by_cases hx : x = [] <;> simp [dropTrans, hx]

/-- A run of `c` with nonempty output is simulated, from the phase `0` or from
the phase `2`, by a run ending in the phase `1` whose output is the output of
the run of `c` with its last letter dropped. -/
lemma drop_complete_drop (c : RelCode) : ∀ (ts : List Tr) (q p : ℕ),
    (codeAut c).Path q ts p → NFAO.outputOf ts ≠ [] → ∀ φ, (φ = 0 ∨ φ = 2) →
    ∃ ts', (codeAut (dropCode c)).Path (3 * q + φ) ts' (3 * p + 1) ∧
      inputOf ts' = inputOf ts ∧ NFAO.outputOf ts' = (NFAO.outputOf ts).dropLast := by
  intro ts
  induction ts with
  | nil =>
      intro q p _ hout _ _
      exact absurd rfl hout
  | cons t ts'' ih =>
      intro q p hpath hout φ hφ
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv hpath
      obtain ⟨p₀, a, x, p₁⟩ := t
      have hsrc' : p₀ = q := hsrc
      subst hsrc'
      by_cases hx : x = []
      · subst hx
        have houtr : NFAO.outputOf ts'' ≠ [] := by simpa using hout
        obtain ⟨ts', hpath', hin', hout'⟩ := ih p₁ p hrest houtr φ hφ
        refine ⟨(3 * p₀ + φ, a, [], 3 * p₁ + φ) :: ts', Path.cons ?_ hpath', by simp [hin'],
          by simp [hout']⟩
        refine mem_dropCode.2 ⟨(p₀, a, [], p₁), hmem, ?_⟩
        rcases hφ with rfl | rfl <;> simp [dropTrans]
      · by_cases hr : NFAO.outputOf ts'' = []
        · obtain ⟨ts', hpath', hin', hout'⟩ :=
            drop_complete_empty c ts'' p₁ p hrest hr 1 (Or.inl rfl)
          refine ⟨(3 * p₀ + φ, a, x.dropLast, 3 * p₁ + 1) :: ts', Path.cons ?_ hpath',
            by simp [hin'], ?_⟩
          · refine mem_dropCode.2 ⟨(p₀, a, x, p₁), hmem, ?_⟩
            rcases hφ with rfl | rfl <;> simp [dropTrans, hx]
          · simp [hout', hr]
        · obtain ⟨ts', hpath', hin', hout'⟩ := ih p₁ p hrest hr 0 (Or.inl rfl)
          refine ⟨(3 * p₀ + φ, a, x, 3 * p₁) :: ts', Path.cons ?_ hpath', by simp [hin'], ?_⟩
          · refine mem_dropCode.2 ⟨(p₀, a, x, p₁), hmem, ?_⟩
            rcases hφ with rfl | rfl <;> simp [dropTrans, hx]
          · simp only [NFAO.outputOf_cons, hout']
            rw [List.dropLast_append_of_ne_nil hr]

/-! ### The relation described by `dropCode` -/

lemma dropTrans_input {t t' : Tr} (h : t' ∈ dropTrans t) : t'.2.1 = t.2.1 := by
  obtain ⟨p₀, a, y, p₁⟩ := t
  by_cases hy : y = []
  · subst hy
    simp [dropTrans] at h
    rcases h with rfl | rfl | rfl <;> rfl
  · simp [dropTrans, hy] at h
    rcases h with rfl | rfl | rfl | rfl <;> rfl

lemma dropTrans_head (t : Tr) :
    (3 * t.1 + 2, t.2.1, (if t.2.2.1 = [] then ([] : List ℕ) else t.2.2.1),
      3 * t.2.2.2 + (if t.2.2.1 = [] then 2 else 0)) ∈ dropTrans t := by
  obtain ⟨p₀, a, y, p₁⟩ := t
  by_cases hy : y = [] <;> simp [dropTrans, hy]

/-- The relation described by `dropCode c`. -/
theorem dropCode_rel (c : RelCode) (w v : List ℕ) :
    codeRel (dropCode c) w v ↔ ∃ u, codeRel c w u ∧ v = u.dropLast := by
  constructor
  · rintro ⟨ts', ⟨Q, hQ, P, hP, hpath⟩, rfl, rfl⟩
    obtain ⟨q, hq, rfl⟩ : ∃ q ∈ c.2.1, 3 * q + 2 = Q := by
      have : Q ∈ (dropCode c).2.1 := hQ
      simpa [dropCode, List.mem_map, eq_comm] using this
    obtain ⟨r, hr, hPr⟩ : ∃ r ∈ c.2.2, P = 3 * r + 2 ∨ P = 3 * r + 1 := by
      have : P ∈ (dropCode c).2.2 := hP
      simpa [dropCode, List.mem_flatMap] using this
    obtain ⟨p, ts, hpath', hin, hcase⟩ := drop_sound_two c ts' q P hpath
    rcases hcase with ⟨hP2, hout, hout'⟩ | ⟨hP0, hout⟩ | ⟨hP1, hne, hout⟩
    · have hpr : p = r := by
        rcases hPr with h | h <;> omega
      subst hpr
      exact ⟨NFAO.outputOf ts, ⟨ts, ⟨q, hq, p, hr, hpath'⟩, hin, rfl⟩, by simp [hout, hout']⟩
    · exfalso
      rcases hPr with h | h <;> omega
    · have hpr : p = r := by
        rcases hPr with h | h <;> omega
      subst hpr
      exact ⟨NFAO.outputOf ts, ⟨ts, ⟨q, hq, p, hr, hpath'⟩, hin, rfl⟩, hout⟩
  · rintro ⟨u, ⟨ts, ⟨q, hq, p, hp, hpath⟩, rfl, rfl⟩, rfl⟩
    by_cases hout : NFAO.outputOf ts = []
    · obtain ⟨ts', hpath', hin', hout'⟩ :=
        drop_complete_empty c ts q p hpath hout 2 (Or.inr rfl)
      refine ⟨ts', ⟨3 * q + 2, ?_, 3 * p + 2, ?_, hpath'⟩, hin', ?_⟩
      · show 3 * q + 2 ∈ (dropCode c).2.1
        exact List.mem_map.2 ⟨q, hq, rfl⟩
      · show 3 * p + 2 ∈ (dropCode c).2.2
        exact List.mem_flatMap.2 ⟨p, hp, by simp⟩
      · rw [hout', hout]
        simp
    · obtain ⟨ts', hpath', hin', hout'⟩ :=
        drop_complete_drop c ts q p hpath hout 2 (Or.inr rfl)
      refine ⟨ts', ⟨3 * q + 2, ?_, 3 * p + 1, ?_, hpath'⟩, hin', hout'⟩
      · show 3 * q + 2 ∈ (dropCode c).2.1
        exact List.mem_map.2 ⟨q, hq, rfl⟩
      · show 3 * p + 1 ∈ (dropCode c).2.2
        exact List.mem_flatMap.2 ⟨p, hp, by simp⟩

/-- `dropCode` does not change the letters that the code can read. -/
theorem dropCode_alphabet (c : RelCode) (x : ℕ) :
    x ∈ codeAlphabet (dropCode c) ↔ x ∈ codeAlphabet c := by
  simp only [codeAlphabet, List.mem_flatMap]
  constructor
  · rintro ⟨t', ht', hx⟩
    obtain ⟨t, ht, hin⟩ := mem_dropCode.1 ht'
    exact ⟨t, ht, by rwa [dropTrans_input hin] at hx⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨_, mem_dropCode.2 ⟨t, ht, dropTrans_head t⟩, ?_⟩
    exact hx

/-- `dropLast` as a composition of primitive recursive list operations. -/
lemma dropLast_eq_reverse_tail_reverse {α : Type} (l : List α) :
    l.dropLast = l.reverse.tail.reverse := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x => simp

lemma primrec_dropLast {α : Type} [Primcodable α] :
    Primrec (fun l : List α => l.dropLast) :=
  (Primrec.list_reverse.comp (Primrec.list_tail.comp Primrec.list_reverse)).of_eq
    (fun l => (dropLast_eq_reverse_tail_reverse l).symm)

/-- A transition of a code is built primitively recursively from its four
components. -/
lemma primrec_mkTr {α : Type} [Primcodable α] {f₁ : α → ℕ} {f₂ f₃ : α → List ℕ} {f₄ : α → ℕ}
    (h₁ : Primrec f₁) (h₂ : Primrec f₂) (h₃ : Primrec f₃) (h₄ : Primrec f₄) :
    Primrec (fun a => ((f₁ a, f₂ a, f₃ a, f₄ a) : Tr)) :=
  h₁.pair (h₂.pair (h₃.pair h₄))

lemma primrec_dropTrans : Primrec dropTrans := by
  have hsrc : Primrec (fun t : Tr => 3 * t.1) :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst
  have htgt : Primrec (fun t : Tr => 3 * t.2.2.2) :=
    Primrec.nat_mul.comp (Primrec.const 3) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hin : Primrec (fun t : Tr => t.2.1) := Primrec.fst.comp Primrec.snd
  have hout : Primrec (fun t : Tr => t.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hnil : Primrec (fun _ : Tr => ([] : List ℕ)) := Primrec.const _
  have hbranch₁ : Primrec (fun t : Tr =>
      [(3 * t.1 + 2, t.2.1, ([] : List ℕ), 3 * t.2.2.2 + 2),
        (3 * t.1, t.2.1, ([] : List ℕ), 3 * t.2.2.2),
        (3 * t.1 + 1, t.2.1, ([] : List ℕ), 3 * t.2.2.2 + 1)]) := by
    refine Primrec.list_cons.comp
      (primrec_mkTr (Primrec.nat_add.comp hsrc (Primrec.const 2)) hin hnil
        (Primrec.nat_add.comp htgt (Primrec.const 2))) ?_
    refine Primrec.list_cons.comp (primrec_mkTr hsrc hin hnil htgt) ?_
    exact Primrec.list_cons.comp
      (primrec_mkTr (Primrec.nat_add.comp hsrc (Primrec.const 1)) hin hnil
        (Primrec.nat_add.comp htgt (Primrec.const 1)))
      (Primrec.const [])
  have hbranch₂ : Primrec (fun t : Tr =>
      [(3 * t.1 + 2, t.2.1, t.2.2.1, 3 * t.2.2.2), (3 * t.1, t.2.1, t.2.2.1, 3 * t.2.2.2),
        (3 * t.1 + 2, t.2.1, t.2.2.1.dropLast, 3 * t.2.2.2 + 1),
        (3 * t.1, t.2.1, t.2.2.1.dropLast, 3 * t.2.2.2 + 1)]) := by
    have hdl : Primrec (fun t : Tr => t.2.2.1.dropLast) := primrec_dropLast.comp hout
    refine Primrec.list_cons.comp
      (primrec_mkTr (Primrec.nat_add.comp hsrc (Primrec.const 2)) hin hout htgt) ?_
    refine Primrec.list_cons.comp (primrec_mkTr hsrc hin hout htgt) ?_
    refine Primrec.list_cons.comp
      (primrec_mkTr (Primrec.nat_add.comp hsrc (Primrec.const 2)) hin hdl
        (Primrec.nat_add.comp htgt (Primrec.const 1))) ?_
    exact Primrec.list_cons.comp
      (primrec_mkTr hsrc hin hdl (Primrec.nat_add.comp htgt (Primrec.const 1)))
      (Primrec.const [])
  refine (Primrec.cond (LenDec.primrec_decEq hout (Primrec.const ([] : List ℕ)))
    hbranch₁ hbranch₂).of_eq ?_
  intro t
  by_cases h : t.2.2.1 = [] <;> simp [dropTrans, h]

lemma primrec_dropCode : Primrec dropCode := by
  refine Primrec.pair (Primrec.list_flatMap Primrec.fst (primrec_dropTrans.comp Primrec.snd).to₂)
    (Primrec.pair ?_ ?_)
  · exact Primrec.list_map (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd)
        (Primrec.const 2)).to₂
  · refine Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) ?_
    have h2 : Primrec (fun z : RelCode × ℕ => 3 * z.2 + 2) :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd) (Primrec.const 2)
    have h1 : Primrec (fun z : RelCode × ℕ => 3 * z.2 + 1) :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd) (Primrec.const 1)
    exact (Primrec.list_cons.comp h2
      (Primrec.list_cons.comp h1 (Primrec.const []))).to₂

/-! ## The code computing `w ↦ f (dropLast w)` -/

/-- The transitions of `shiftCode`: those of the code, and one reading a letter
and writing nothing from every final state into a fresh state. -/
def shiftTrans (c : RelCode) : List Tr :=
  c.1 ++ c.2.2.flatMap (fun p =>
    (codeAlphabet c).map (fun a => (p, [a], ([] : List ℕ), CodeMerge.freshF c)))

/-- The code computing `w ↦ f (dropLast w)`. -/
def shiftCode (c : RelCode) : RelCode :=
  (shiftTrans c, (CodeMerge.freshF c + 1) :: c.2.1,
    [CodeMerge.freshF c, CodeMerge.freshF c + 1])

/-! ### The transitions of `shiftCode` -/

lemma inputOf_append (ts ts' : List Tr) :
    inputOf (ts ++ ts') = inputOf ts ++ inputOf ts' := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

lemma outputOf_append (ts ts' : List Tr) :
    NFAO.outputOf (ts ++ ts') = NFAO.outputOf ts ++ NFAO.outputOf ts' := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

/-- Every state occurring in a code is smaller than the fresh state. -/
lemma lt_freshF {c : RelCode} {x : ℕ}
    (h : x ∈ c.2.1 ++ c.2.2 ++ c.1.map (fun t => t.1) ++ c.1.map (fun t => t.2.2.2)) :
    x < CodeMerge.freshF c := by
  have := le_foldr_max h
  simp only [CodeMerge.freshF]
  omega

lemma mem_shiftCode {c : RelCode} {t : Tr} :
    t ∈ (shiftCode c).1 ↔
      (t ∈ c.1 ∨ ∃ p ∈ c.2.2, ∃ a ∈ codeAlphabet c,
        t = (p, [a], ([] : List ℕ), CodeMerge.freshF c)) := by
  simp [shiftCode, shiftTrans, List.mem_flatMap, eq_comm]

/-- The fresh states are not the source of any transition of `shiftCode c`. -/
lemma shift_src_ne {c : RelCode} {t : Tr} (ht : t ∈ (shiftCode c).1) :
    t.1 ≠ CodeMerge.freshF c ∧ t.1 ≠ CodeMerge.freshF c + 1 := by
  have hlt : t.1 < CodeMerge.freshF c := by
    rcases mem_shiftCode.1 ht with h | ⟨p, hp, a, -, rfl⟩
    · exact lt_freshF (by
        simp only [List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨t, h, rfl⟩))
    · exact lt_freshF (by simp [hp])
  exact ⟨by omega, by omega⟩

/-- No transition of `shiftCode c` leaves a fresh state. -/
lemma shift_path_fresh {c : RelCode} {ts : List Tr} {P k : ℕ}
    (hk : k = CodeMerge.freshF c ∨ k = CodeMerge.freshF c + 1)
    (h : (codeAut (shiftCode c)).Path k ts P) : ts = [] ∧ P = k := by
  rcases ts with _ | ⟨t, ts⟩
  · exact ⟨rfl, (Path.eq_of_nil h).symm⟩
  · obtain ⟨hsrc, hmem, -⟩ := Path.cons_inv h
    obtain ⟨h1, h2⟩ := shift_src_ne (show t ∈ (shiftCode c).1 from hmem)
    rcases hk with rfl | rfl
    · exact absurd hsrc h1
    · exact absurd hsrc h2

/-- Every state on a path of a code is smaller than the fresh state. -/
lemma path_lt_freshF {c : RelCode} : ∀ {ts : List Tr} {q p : ℕ},
    (codeAut c).Path q ts p → q < CodeMerge.freshF c → p < CodeMerge.freshF c := by
  intro ts
  induction ts with
  | nil => intro q p h hq; exact (Path.eq_of_nil h) ▸ hq
  | cons t ts ih =>
      intro q p h _
      obtain ⟨-, hmem, hrest⟩ := Path.cons_inv h
      exact ih hrest (lt_freshF (by
        simp only [List.mem_append, List.mem_map]
        exact Or.inr ⟨t, hmem, rfl⟩))

/-- A run of `c` is a run of `shiftCode c`. -/
lemma shift_path_of_code {c : RelCode} : ∀ {ts : List Tr} {q p : ℕ},
    (codeAut c).Path q ts p → (codeAut (shiftCode c)).Path q ts p := by
  intro ts
  induction ts with
  | nil => intro q p h; exact (Path.eq_of_nil h) ▸ Path.nil q
  | cons t ts ih =>
      intro q p h
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv h
      obtain ⟨p₀, a, x, p₁⟩ := t
      have : p₀ = q := hsrc
      subst this
      exact Path.cons (mem_shiftCode.2 (Or.inl hmem)) (ih hrest)

/-! ### The relation described by `shiftCode` -/

/-- A run of `shiftCode c` from a state of `c` either is a run of `c`, or is a
run of `c` ending in a final state followed by the extra transition. -/
lemma shift_sound (c : RelCode) : ∀ (ts' : List Tr) (q P : ℕ),
    (codeAut (shiftCode c)).Path q ts' P → q < CodeMerge.freshF c →
    ((codeAut c).Path q ts' P ∧ P < CodeMerge.freshF c) ∨
      (∃ (ts : List Tr) (a p : ℕ),
        ts' = ts ++ [(p, [a], ([] : List ℕ), CodeMerge.freshF c)] ∧
        P = CodeMerge.freshF c ∧ p ∈ c.2.2 ∧ a ∈ codeAlphabet c ∧
        (codeAut c).Path q ts p) := by
  intro ts'
  induction ts' with
  | nil =>
      intro q P h hq
      exact Or.inl ⟨(Path.eq_of_nil h) ▸ Path.nil q, (Path.eq_of_nil h) ▸ hq⟩
  | cons t ts'' ih =>
      intro q P h hq
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv h
      rcases mem_shiftCode.1 (show t ∈ (shiftCode c).1 from hmem) with hc | ⟨p, hp, a, ha, rfl⟩
      · have htgt : t.2.2.2 < CodeMerge.freshF c :=
          lt_freshF (by
            simp only [List.mem_append, List.mem_map]
            exact Or.inr ⟨t, hc, rfl⟩)
        rcases ih t.2.2.2 P hrest htgt with ⟨hpath, hP⟩ | ⟨ts, a, r, hts, hP, hr, ha, hpath⟩
        · refine Or.inl ⟨?_, hP⟩
          rw [← hsrc]
          exact Path.cons (show (t.1, t.2.1, t.2.2.1, t.2.2.2) ∈ (codeAut c).δ from hc) hpath
        · refine Or.inr ⟨t :: ts, a, r, by rw [hts]; rfl, hP, hr, ha, ?_⟩
          rw [← hsrc]
          exact Path.cons (show (t.1, t.2.1, t.2.2.1, t.2.2.2) ∈ (codeAut c).δ from hc) hpath
      · obtain ⟨hnil, hPeq⟩ := shift_path_fresh (Or.inl rfl) hrest
        subst hnil
        refine Or.inr ⟨[], a, p, rfl, hPeq, hp, ha, ?_⟩
        rw [← hsrc]
        exact Path.nil p

/-- The relation described by `shiftCode c`. -/
theorem shiftCode_rel (c : RelCode) (w v : List ℕ) :
    codeRel (shiftCode c) w v ↔
      ((w = [] ∧ v = []) ∨ ∃ u a, w = u ++ [a] ∧ a ∈ codeAlphabet c ∧ codeRel c u v) := by
  constructor
  · rintro ⟨ts', ⟨Q, hQ, P, hP, hpath⟩, rfl, rfl⟩
    have hQ' : Q = CodeMerge.freshF c + 1 ∨ Q ∈ c.2.1 := by
      have : Q ∈ (shiftCode c).2.1 := hQ
      simpa [shiftCode] using this
    have hP' : P = CodeMerge.freshF c ∨ P = CodeMerge.freshF c + 1 := by
      have : P ∈ (shiftCode c).2.2 := hP
      simpa [shiftCode] using this
    rcases hQ' with rfl | hq
    · obtain ⟨hnil, -⟩ := shift_path_fresh (Or.inr rfl) hpath
      subst hnil
      exact Or.inl ⟨rfl, rfl⟩
    · have hqlt : Q < CodeMerge.freshF c := lt_freshF (by simp [hq])
      rcases shift_sound c ts' Q P hpath hqlt with ⟨hpath', hPlt⟩ | ⟨ts, a, p, rfl, hPeq, hp, ha, hpath'⟩
      · exfalso
        rcases hP' with rfl | rfl <;> omega
      · refine Or.inr ⟨inputOf ts, a, ?_, ha,
          ⟨ts, ⟨Q, hq, p, hp, hpath'⟩, rfl, by rw [outputOf_append]; simp⟩⟩
        rw [inputOf_append]
        simp [inputOf]
  · rintro (⟨rfl, rfl⟩ | ⟨u, a, rfl, ha, ⟨ts, ⟨q, hq, p, hp, hpath⟩, rfl, rfl⟩⟩)
    · refine ⟨[], ⟨CodeMerge.freshF c + 1, ?_, CodeMerge.freshF c + 1, ?_, Path.nil _⟩, rfl, rfl⟩
      · show CodeMerge.freshF c + 1 ∈ (shiftCode c).2.1
        simp [shiftCode]
      · show CodeMerge.freshF c + 1 ∈ (shiftCode c).2.2
        simp [shiftCode]
    · refine ⟨ts ++ [(p, [a], ([] : List ℕ), CodeMerge.freshF c)],
        ⟨q, ?_, CodeMerge.freshF c, ?_, ?_⟩, ?_, ?_⟩
      · show q ∈ (shiftCode c).2.1
        simp only [shiftCode, List.mem_cons]
        exact Or.inr hq
      · show CodeMerge.freshF c ∈ (shiftCode c).2.2
        simp [shiftCode]
      · refine Path.append (r := p) (ts' := [(p, [a], ([] : List ℕ), CodeMerge.freshF c)]) ?_ ?_
        · exact shift_path_of_code hpath
        · exact Path.cons (mem_shiftCode.2 (Or.inr ⟨p, hp, a, ha, rfl⟩)) (Path.nil _)
      · rw [inputOf_append]
        simp [inputOf]
      · rw [outputOf_append]
        simp

/-- `shiftCode` does not change the letters that the code can read. -/
theorem shiftCode_alphabet (c : RelCode) (x : ℕ) :
    x ∈ codeAlphabet (shiftCode c) ↔ x ∈ codeAlphabet c := by
  simp only [codeAlphabet, List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hx⟩
    rcases mem_shiftCode.1 ht with hc | ⟨p, hp, a, ha, rfl⟩
    · exact ⟨t, hc, hx⟩
    · have : x = a := by simpa using hx
      subst this
      exact List.mem_flatMap.1 ha
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, mem_shiftCode.2 (Or.inl ht), hx⟩

lemma primrec_shiftTrans : Primrec shiftTrans := by
  have hinner : Primrec (fun z : (RelCode × ℕ) × ℕ =>
      ((z.1.2, [z.2], ([] : List ℕ), CodeMerge.freshF z.1.1) : Tr)) :=
    primrec_mkTr (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (Primrec.const ([] : List ℕ))
      (CodeMerge.primrec_freshF.comp (Primrec.fst.comp Primrec.fst))
  have houter : Primrec (fun z : RelCode × ℕ =>
      (codeAlphabet z.1).map
        (fun a => ((z.2, [a], ([] : List ℕ), CodeMerge.freshF z.1) : Tr))) :=
    Primrec.list_map (primrec_codeAlphabet.comp Primrec.fst) hinner.to₂
  exact Primrec.list_append.comp Primrec.fst
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) houter.to₂)

lemma primrec_shiftCode : Primrec shiftCode := by
  have hfresh : Primrec (fun c : RelCode => CodeMerge.freshF c) := CodeMerge.primrec_freshF
  have hfresh1 : Primrec (fun c : RelCode => CodeMerge.freshF c + 1) :=
    Primrec.nat_add.comp hfresh (Primrec.const 1)
  exact Primrec.pair primrec_shiftTrans
    (Primrec.pair (Primrec.list_cons.comp hfresh1 (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp hfresh (Primrec.list_cons.comp hfresh1 (Primrec.const []))))

/-! ## The two codes describe functions -/

/-- Under the promise, `dropCode c` describes a total function on the strings
over its alphabet. -/
theorem codeFunctional_dropCode {c : RelCode} (hc : CodeFunctional c) :
    CodeFunctional (dropCode c) := by
  intro w hw
  have hw' : CodeWord c w := fun x hx => (dropCode_alphabet c x).1 (hw x hx)
  obtain ⟨u, hu, huniq⟩ := hc w hw'
  refine ⟨u.dropLast, (dropCode_rel c w _).2 ⟨u, hu, rfl⟩, ?_⟩
  rintro v hv
  obtain ⟨u', hu', rfl⟩ := (dropCode_rel c w v).1 hv
  rw [huniq u' hu']

/-- Under the promise, `shiftCode c` describes a total function on the strings
over its alphabet. -/
theorem codeFunctional_shiftCode {c : RelCode} (hc : CodeFunctional c) :
    CodeFunctional (shiftCode c) := by
  intro w hw
  have hw' : CodeWord c w := fun x hx => (shiftCode_alphabet c x).1 (hw x hx)
  rcases List.eq_nil_or_concat' w with rfl | ⟨u, a, rfl⟩
  · refine ⟨[], (shiftCode_rel c [] []).2 (Or.inl ⟨rfl, rfl⟩), ?_⟩
    rintro v hv
    rcases (shiftCode_rel c [] v).1 hv with ⟨-, rfl⟩ | ⟨u', a', hcontra, -, -⟩
    · rfl
    · exact absurd hcontra.symm (by simp)
  · have hu : CodeWord c u := fun x hx => hw' x (by simp [hx])
    have ha : a ∈ codeAlphabet c := hw' a (by simp)
    obtain ⟨v, hv, huniq⟩ := hc u hu
    refine ⟨v, (shiftCode_rel c _ v).2 (Or.inr ⟨u, a, rfl, ha, hv⟩), ?_⟩
    rintro v' hv'
    rcases (shiftCode_rel c _ v').1 hv' with ⟨hcontra, -⟩ | ⟨u', a', heq, -, hrel⟩
    · simp at hcontra
    · obtain ⟨rfl, -⟩ := List.append_inj' heq rfl
      exact huniq v' hrel

/-! ## Prefix preservation as the equality of the two coded functions -/

/-- The property that the relation described by a code is prefix preserving. -/
def PrefixCrit (c : RelCode) : Prop :=
  ∀ (w : List ℕ) (v : List ℕ) (a : ℕ) (u : List ℕ),
    codeRel c w v → codeRel c (w ++ [a]) u → v <+: u

/-- A prefix of length one less than the whole string is its `dropLast`. -/
lemma eq_dropLast_of_prefix {v u : List ℕ} (h : v <+: u) (hl : v.length + 1 = u.length) :
    v = u.dropLast := by
  have h1 : v = u.take v.length := List.prefix_iff_eq_take.1 h
  have h2 : u.dropLast = u.take (u.length - 1) := List.dropLast_eq_take
  rw [h1, h2]
  congr 1
  omega

/-- Under the promise and length preservation, the coded function is prefix
preserving exactly when the two codes above describe the same relation. -/
theorem prefixCrit_iff {c : RelCode} (hc : CodeFunctional c)
    (hlen : ∀ w v, codeRel c w v → v.length = w.length) :
    PrefixCrit c ↔ codeRel (dropCode c) = codeRel (shiftCode c) := by
  constructor
  · intro hpre
    funext w v
    apply propext
    constructor
    · intro hd
      obtain ⟨u, hu, rfl⟩ := (dropCode_rel c w v).1 hd
      have hw : CodeWord c w := codeRel_codeWord hu
      rcases List.eq_nil_or_concat' w with rfl | ⟨w', a, rfl⟩
      · have hnil : u = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen _ _ hu)
        subst hnil
        exact (shiftCode_rel c [] []).2 (Or.inl ⟨rfl, rfl⟩)
      · have ha : a ∈ codeAlphabet c := hw a (by simp)
        have hw' : CodeWord c w' := fun x hx => hw x (by simp [hx])
        obtain ⟨v', hv', -⟩ := hc w' hw'
        have hprefix : v' <+: u := hpre w' v' a u hv' hu
        have hlu : u.length = w'.length + 1 := by simpa using hlen _ _ hu
        have hlv : v'.length = w'.length := hlen _ _ hv'
        have hdl : v' = u.dropLast := eq_dropLast_of_prefix hprefix (by omega)
        rw [← hdl]
        exact (shiftCode_rel c _ v').2 (Or.inr ⟨w', a, rfl, ha, hv'⟩)
    · intro hs
      rcases (shiftCode_rel c w v).1 hs with ⟨rfl, rfl⟩ | ⟨u, a, rfl, ha, hrel⟩
      · obtain ⟨z, hz, -⟩ := hc [] (by intro x hx; simp at hx)
        have hnil : z = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen _ _ hz)
        exact (dropCode_rel c [] []).2 ⟨z, hz, by simp [hnil]⟩
      · have hu : CodeWord c u := codeRel_codeWord hrel
        have hwa : CodeWord c (u ++ [a]) := by
          intro x hx
          rcases List.mem_append.1 hx with hx' | hx'
          · exact hu x hx'
          · have hxa : x = a := by simpa using hx'
            exact hxa ▸ ha
        obtain ⟨z, hz, -⟩ := hc (u ++ [a]) hwa
        have hprefix : v <+: z := hpre u v a z hrel hz
        have hlz : z.length = u.length + 1 := by simpa using hlen _ _ hz
        have hlv : v.length = u.length := hlen _ _ hrel
        exact (dropCode_rel c _ v).2 ⟨z, hz, eq_dropLast_of_prefix hprefix (by omega)⟩
  · intro heq w v a u hwv hwau
    have hcw : CodeWord c (w ++ [a]) := codeRel_codeWord hwau
    have ha : a ∈ codeAlphabet c := hcw a (by simp)
    have h1 : codeRel (shiftCode c) (w ++ [a]) v :=
      (shiftCode_rel c _ v).2 (Or.inr ⟨w, a, rfl, ha, hwv⟩)
    rw [← heq] at h1
    obtain ⟨u', hu', rfl⟩ := (dropCode_rel c _ v).1 h1
    obtain ⟨z, -, huniq⟩ := hc _ hcw
    rw [huniq u' hu', huniq u hwau]
    exact List.dropLast_prefix z

end PrefixCodes
end Lax132576Proofs.Transducers
