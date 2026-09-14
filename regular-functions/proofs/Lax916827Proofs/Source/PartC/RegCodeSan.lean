/- Codes of two-way transducers (Section *Decidability of equivalence* of *Transducers*, M.
Bojańczyk) and the behaviour of a coded transducer on letters that do not occur in its transition
table.

The definitions of `TwoWayCode`, `twoWayCodeAut`, `twoWayCodeRel` and `TwoWayCodeTotal` used to be
in `RequestProject/PartC/Statements.lean`; they are given here, unchanged, so that the decision
procedure of Theorem `thm:decidable-equivalence-regular` can be developed before that file.

A code is a finite lookup table, so it mentions only finitely many letters, and a transition whose
adjacent letters are not both mentioned by the table is absent from it and therefore halts with
empty output.  Consequently the behaviour of a coded transducer does not distinguish between two
letters that are both absent from the table: renaming the letters of the input by any map which
fixes the letters of the table and sends the other letters to letters outside the table does not
change the computed relation (`Transducers.RegDec.twoWayCodeRel_map`).  This is what makes the
equivalence test of Theorem `thm:decidable-equivalence-regular` a *finite* check: it is enough to
compare the two coded transducers on the short strings over the letters of the two tables together
with one fresh letter. -/
import Lax916827Proofs.Source.PartC.TwoWayCont
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- A finite description of a two-way transducer with states and letters coded
by natural numbers. -/
abbrev TwoWayCode := List ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool)))

/-- The two-way transducer described by a code. -/
def twoWayCodeAut (c : TwoWayCode) : TwoWay ℕ ℕ ℕ where
  init := 0
  step := fun l q r =>
    match c.lookup (l, q, r) with
    | some x => x
    | none => Sum.inl []

/-- The relation computed by the two-way transducer described by a code. -/
def twoWayCodeRel (c : TwoWayCode) : List ℕ → List ℕ → Prop := (twoWayCodeAut c).Computes

/-- The promise that a code describes a transducer that computes a total
function. -/
def TwoWayCodeTotal (c : TwoWayCode) : Prop := ∀ w, ∃ v, twoWayCodeRel c w v

namespace RegDec

/-! ## The letters of a code -/

/-- The input letters occurring in the transition table of a code (together
with the letter `0`, which is thrown in so that the list is a plain `flatMap`
of two entries per transition, and which only makes the list larger). -/
def alphabet (c : TwoWayCode) : List ℕ :=
  c.flatMap (fun t => [t.1.1.getD 0, t.1.2.2.getD 0])

lemma mem_alphabet_left {c : TwoWayCode} {t} (ht : t ∈ c) {x : ℕ}
    (hx : t.1.1 = some x) : x ∈ alphabet c := by
  refine List.mem_flatMap.2 ⟨t, ht, ?_⟩
  simp [hx]

lemma mem_alphabet_right {c : TwoWayCode} {t} (ht : t ∈ c) {x : ℕ}
    (hx : t.1.2.2 = some x) : x ∈ alphabet c := by
  refine List.mem_flatMap.2 ⟨t, ht, ?_⟩
  simp [hx]

/-- A key whose left letter is not a letter of the code is absent from it. -/
lemma lookup_eq_none_left {c : TwoWayCode} {x : ℕ} (hx : x ∉ alphabet c) (q : ℕ)
    (r : Option ℕ) : c.lookup (some x, q, r) = none := by
  refine List.lookup_eq_none_iff.2 ?_
  intro p hp
  simp only [bne_iff_ne, ne_eq]
  intro h
  exact hx (mem_alphabet_left hp (by rw [← h]))

/-- A key whose right letter is not a letter of the code is absent from it. -/
lemma lookup_eq_none_right {c : TwoWayCode} {x : ℕ} (hx : x ∉ alphabet c) (q : ℕ)
    (l : Option ℕ) : c.lookup (l, q, some x) = none := by
  refine List.lookup_eq_none_iff.2 ?_
  intro p hp
  simp only [bne_iff_ne, ne_eq]
  intro h
  exact hx (mem_alphabet_right hp (by rw [← h]))

/-! ## Renaming the letters outside the code -/

/-- A renaming of the letters which the code cannot see: it fixes the letters
of the transition table and keeps the other letters outside the table. -/
structure Blind (c : TwoWayCode) (σ : ℕ → ℕ) : Prop where
  /-- The letters of the table are fixed. -/
  fix : ∀ x ∈ alphabet c, σ x = x
  /-- The other letters stay outside the table. -/
  out : ∀ x, x ∉ alphabet c → σ x ∉ alphabet c

lemma Blind.map_option {c : TwoWayCode} {σ : ℕ → ℕ} (hσ : Blind c σ) {l : Option ℕ}
    (hl : ∀ x ∈ l, x ∈ alphabet c) : l.map σ = l := by
  cases l with
  | none => rfl
  | some x => simp [hσ.fix x (hl x rfl)]

/-- The renamed transition is the original transition. -/
lemma step_map {c : TwoWayCode} {σ : ℕ → ℕ} (hσ : Blind c σ) (l : Option ℕ) (q : ℕ)
    (r : Option ℕ) :
    (twoWayCodeAut c).step (l.map σ) q (r.map σ) = (twoWayCodeAut c).step l q r := by
  by_cases hl : ∀ x ∈ l, x ∈ alphabet c
  · by_cases hr : ∀ x ∈ r, x ∈ alphabet c
    · rw [hσ.map_option hl, hσ.map_option hr]
    · push_neg at hr
      obtain ⟨x, hxr, hx⟩ := hr
      have hrx : r = some x := hxr
      subst hrx
      have h1 : c.lookup (l.map σ, q, some (σ x)) = none :=
        lookup_eq_none_right (hσ.out x hx) q _
      have h2 : c.lookup (l, q, some x) = none := lookup_eq_none_right hx q _
      simp only [twoWayCodeAut, Option.map_some, h1, h2]
  · push_neg at hl
    obtain ⟨x, hxl, hx⟩ := hl
    have hlx : l = some x := hxl
    subst hlx
    have h1 : c.lookup (some (σ x), q, r.map σ) = none :=
      lookup_eq_none_left (hσ.out x hx) q _
    have h2 : c.lookup (some x, q, r) = none := lookup_eq_none_left hx q _
    simp only [twoWayCodeAut, Option.map_some, h1, h2]

/-- The renaming of a configuration: the letters of the input are renamed, the
state and the position of the head are kept. -/
def mapCfg (σ : ℕ → ℕ) : Cfg ℕ ℕ → Cfg ℕ ℕ
  | Cfg.conf u q v => Cfg.conf (u.map σ) q (v.map σ)
  | Cfg.halt => Cfg.halt

@[simp] lemma mapCfg_halt (σ : ℕ → ℕ) : mapCfg σ Cfg.halt = Cfg.halt := rfl

lemma eq_halt_of_mapCfg_eq_halt {σ : ℕ → ℕ} {x : Cfg ℕ ℕ} (h : mapCfg σ x = Cfg.halt) :
    x = Cfg.halt := by
  cases x with
  | halt => rfl
  | conf u q v => simp [mapCfg] at h

/-- One step of the renamed run is the renaming of one step of the run. -/
lemma stepCfg_mapCfg {c : TwoWayCode} {σ : ℕ → ℕ} (hσ : Blind c σ) (x : Cfg ℕ ℕ) :
    (twoWayCodeAut c).stepCfg (mapCfg σ x) =
      ((twoWayCodeAut c).stepCfg x).map (fun p => (p.1, mapCfg σ p.2)) := by
  cases x with
  | halt => simp [mapCfg, TwoWay.stepCfg]
  | conf u q v =>
      have hu : (u.map σ).getLast? = u.getLast?.map σ := by
        rw [List.getLast?_map]
      have hv : (v.map σ).head? = v.head?.map σ := by
        rw [List.head?_map]
      simp only [mapCfg, TwoWay.stepCfg, hu, hv, step_map hσ]
      rcases hstep : (twoWayCodeAut c).step u.getLast? q v.head? with o | ⟨q', o, dir⟩
      · simp
      · cases dir with
        | true =>
            cases v with
            | nil => simp
            | cons a v' => simp
        | false =>
            cases hgl : u.getLast? with
            | none => simp
            | some a =>
                simp only [Option.map_some]
                have hdl : (u.map σ).dropLast = u.dropLast.map σ := List.map_dropLast.symm
                simp only [List.map_cons, hdl]

/-- A run of the renamed configuration is the renaming of a run. -/
lemma reaches_mapCfg_of_reaches {c : TwoWayCode} {σ : ℕ → ℕ} (hσ : Blind c σ)
    {x y : Cfg ℕ ℕ} {o : List ℕ} (h : (twoWayCodeAut c).Reaches x o y) :
    (twoWayCodeAut c).Reaches (mapCfg σ x) o (mapCfg σ y) := by
  induction h with
  | refl x => exact TwoWay.Reaches.refl _
  | step hstep _ ih =>
      refine TwoWay.Reaches.step ?_ ih
      rw [stepCfg_mapCfg hσ, hstep]
      rfl

/-- Conversely, every run of a renamed configuration comes from a run. -/
lemma reaches_of_reaches_mapCfg {c : TwoWayCode} {σ : ℕ → ℕ} (hσ : Blind c σ)
    {x z : Cfg ℕ ℕ} {o : List ℕ} (h : (twoWayCodeAut c).Reaches (mapCfg σ x) o z) :
    ∃ y, z = mapCfg σ y ∧ (twoWayCodeAut c).Reaches x o y := by
  generalize hx : mapCfg σ x = x' at h
  induction h generalizing x with
  | refl x' => exact ⟨x, hx.symm, TwoWay.Reaches.refl _⟩
  | @step c₁ c₂ c₃ o₁ o₂ hstep _ ih =>
      subst hx
      rw [stepCfg_mapCfg hσ] at hstep
      rcases hx' : (twoWayCodeAut c).stepCfg x with _ | ⟨o', x''⟩
      · rw [hx'] at hstep; simp at hstep
      · rw [hx'] at hstep
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨ho, hc2⟩ := hstep
        obtain ⟨y, hy, hreach⟩ := ih (x := x'') hc2
        exact ⟨y, hy, TwoWay.Reaches.step (by rw [hx', ← ho]) hreach⟩

/-- **The code is blind to the letters outside its table.**  Renaming the input
letters by a map that fixes the letters of the table and keeps the other letters
outside it does not change the computed relation. -/
theorem twoWayCodeRel_map {c : TwoWayCode} {σ : ℕ → ℕ} (hσ : Blind c σ) (w v : List ℕ) :
    twoWayCodeRel c (w.map σ) v ↔ twoWayCodeRel c w v := by
  constructor
  · intro h
    have h' : (twoWayCodeAut c).Reaches (mapCfg σ (Cfg.conf [] (twoWayCodeAut c).init w)) v
        Cfg.halt := by simpa [mapCfg] using h
    obtain ⟨y, hy, hreach⟩ := reaches_of_reaches_mapCfg hσ h'
    have hyh : y = Cfg.halt := eq_halt_of_mapCfg_eq_halt hy.symm
    subst hyh
    exact hreach
  · intro h
    have := reaches_mapCfg_of_reaches (σ := σ) hσ h
    simpa [mapCfg] using this

/-! ## A letter outside a finite set -/

/-- A letter that does not occur in the list `L`. -/
def freshLetter (L : List ℕ) : ℕ := L.foldr max 0 + 1

lemma le_foldr_max {L : List ℕ} {x : ℕ} (hx : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at hx
  | cons a t ih =>
      rcases List.mem_cons.1 hx with rfl | hx'
      · simp
      · exact le_trans (ih hx') (by simp)

lemma freshLetter_not_mem (L : List ℕ) : freshLetter L ∉ L := by
  intro h
  have hle := le_foldr_max h
  simp only [freshLetter] at hle
  omega

/-! ## Renaming the letters outside the two codes -/

/-- The letters used by the test: those of the two codes, together with one
fresh letter standing for all the others. -/
def testAlphabet (p : TwoWayCode × TwoWayCode) : List ℕ :=
  freshLetter (alphabet p.1 ++ alphabet p.2) :: (alphabet p.1 ++ alphabet p.2)

/-- The renaming that keeps the letters of the two codes and sends every other
letter to the fresh letter. -/
def sanLetter (p : TwoWayCode × TwoWayCode) (x : ℕ) : ℕ :=
  if x ∈ alphabet p.1 ++ alphabet p.2 then x else freshLetter (alphabet p.1 ++ alphabet p.2)

lemma sanLetter_mem_testAlphabet (p : TwoWayCode × TwoWayCode) (x : ℕ) :
    sanLetter p x ∈ testAlphabet p := by
  unfold sanLetter testAlphabet
  split
  · exact List.mem_cons_of_mem _ ‹_›
  · exact List.mem_cons_self

lemma blind_sanLetter_left (p : TwoWayCode × TwoWayCode) : Blind p.1 (sanLetter p) := by
  constructor
  · intro x hx
    simp [sanLetter, List.mem_append.2 (Or.inl hx)]
  · intro x hx
    by_cases hmem : x ∈ alphabet p.1 ++ alphabet p.2
    · simpa [sanLetter, hmem] using hx
    · intro hcon
      have : freshLetter (alphabet p.1 ++ alphabet p.2) ∈ alphabet p.1 ++ alphabet p.2 :=
        List.mem_append.2 (Or.inl (by simpa [sanLetter, hmem] using hcon))
      exact freshLetter_not_mem _ this

lemma blind_sanLetter_right (p : TwoWayCode × TwoWayCode) : Blind p.2 (sanLetter p) := by
  constructor
  · intro x hx
    simp [sanLetter, List.mem_append.2 (Or.inr hx)]
  · intro x hx
    by_cases hmem : x ∈ alphabet p.1 ++ alphabet p.2
    · simpa [sanLetter, hmem] using hx
    · intro hcon
      have : freshLetter (alphabet p.1 ++ alphabet p.2) ∈ alphabet p.1 ++ alphabet p.2 :=
        List.mem_append.2 (Or.inr (by simpa [sanLetter, hmem] using hcon))
      exact freshLetter_not_mem _ this

end RegDec

end Lax916827Proofs.Transducers
