/-
A toolkit of regular languages, used for the automata constructions of
Section *Logic* of *Transducers* (M. Bojańczyk).

Mathlib provides closure of `Language.IsRegular` under Boolean operations; the
facts collected here are the remaining ones that the translation of monadic
second-order formulas into automata needs:

* a language defined by a `foldl` over a finite state space is regular
  (`isRegular_foldl`), and the language of an nfa with finitely many states is
  regular (`isRegular_of_nfa`);
* regular languages are closed under inverse images (`isRegular_comap`) and
  images (`isRegular_image`) of letter-to-letter maps — the image is the
  projection that interprets an existential quantifier;
* the three elementary "scanning" languages used for the atomic formulas:
  the first position satisfying `P` also satisfies `R` (`isRegular_scan`), the
  first position satisfying `P` comes before the first position satisfying `Q`
  (`isRegular_findIdx_le`), and `P` holds in exactly one position
  (`isRegular_countP_eq_one`).
-/
import Lax765601Proofs.Source.Common.Basic
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace RegAut

variable {Γ Δ : Type}

/-! ## Automata -/

/-- A language defined by a `foldl` over a finite state space is regular. -/
lemma isRegular_foldl {S : Type} [Finite S] (step : S → Γ → S) (s0 : S) (acc : Set S) :
    Language.IsRegular {u : List Γ | u.foldl step s0 ∈ acc} := by
  letI : Fintype S := Fintype.ofFinite S
  exact ⟨S, inferInstance, ⟨step, s0, acc⟩, rfl⟩

/-- The language of a nondeterministic automaton with finitely many states is
regular. -/
lemma isRegular_of_nfa {S : Type} [Finite S] (N : NFA Γ S) : N.accepts.IsRegular := by
  letI : Fintype S := Fintype.ofFinite S
  exact ⟨Set S, inferInstance, N.toDFA, NFA.toDFA_correct⟩

/-! ## Boolean operations -/

lemma isRegular_univ : Language.IsRegular (Set.univ : Language Γ) := by
  have := isRegular_foldl (Γ := Γ) (fun (_ : Unit) _ => ()) () Set.univ
  simpa using this

lemma isRegular_and {L₁ L₂ : Language Γ} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    Language.IsRegular {u | u ∈ L₁ ∧ u ∈ L₂} := by
  have := h₁.inf h₂
  convert this using 1

lemma isRegular_or {L₁ L₂ : Language Γ} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    Language.IsRegular {u | u ∈ L₁ ∨ u ∈ L₂} := by
  have := h₁.add h₂
  convert this using 1

lemma isRegular_not {L : Language Γ} (h : L.IsRegular) : Language.IsRegular {u | u ∉ L} := by
  have := h.compl
  convert this using 1

/-- Regularity is transported along an equality of languages. -/
lemma isRegular_of_eq {L₁ L₂ : Language Γ} (h : L₁.IsRegular) (he : ∀ u, u ∈ L₂ ↔ u ∈ L₁) :
    L₂.IsRegular := by
  have hEq : L₂ = L₁ := Set.ext he
  rw [hEq]
  exact h

/-- Regularity of a finite intersection, indexed by the entries of a list. -/
lemma isRegular_forall_list {ι : Type} (L : ι → Language Γ) :
    ∀ (l : List ι), (∀ x ∈ l, (L x).IsRegular) →
      Language.IsRegular {u : List Γ | ∀ x ∈ l, u ∈ L x}
  | [], _ => by simpa using isRegular_univ (Γ := Γ)
  | x :: l, h => by
      have hx : (L x).IsRegular := h x (by simp)
      have hl := isRegular_forall_list L l (fun y hy => h y (by simp [hy]))
      have := isRegular_and hx hl
      convert this using 1
      ext u
      simp only [List.mem_cons]
      constructor
      · intro hu; exact ⟨hu x (Or.inl rfl), fun y hy => hu y (Or.inr hy)⟩
      · rintro ⟨h1, h2⟩ y (rfl | hy)
        · exact h1
        · exact h2 y hy

/-! ## Images and inverse images of letter-to-letter maps -/

/-- The inverse image of a regular language under a letter-to-letter map is
regular. -/
lemma isRegular_comap (h : Γ → Δ) {L : Language Δ} (hL : L.IsRegular) :
    Language.IsRegular {u : List Γ | u.map h ∈ L} := by
  obtain ⟨σ, hσ, D, rfl⟩ := hL
  refine ⟨σ, hσ, ⟨fun q a => D.step q (h a), D.start, D.accept⟩, ?_⟩
  have key : ∀ (u : List Γ) (q : σ),
      List.foldl (fun q a => D.step q (h a)) q u = List.foldl D.step q (u.map h) := by
    intro u
    induction u with
    | nil => intro q; rfl
    | cons a u ih => intro q; simpa using ih (D.step q (h a))
  ext u
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom]
  rw [key]
  rfl

/-- The image of a regular language under a letter-to-letter map is regular. -/
lemma isRegular_image (h : Γ → Δ) {L : Language Γ} (hL : L.IsRegular) :
    Language.IsRegular {v : List Δ | ∃ u, u ∈ L ∧ u.map h = v} := by
  obtain ⟨σ, hσ, D, rfl⟩ := hL
  set N : NFA Δ σ := ⟨fun q c => {q' | ∃ a, h a = c ∧ q' = D.step q a}, {D.start}, D.accept⟩
    with hN
  have key : ∀ (v : List Δ) (q : σ),
      N.evalFrom {q} v = {q' | ∃ u : List Γ, u.map h = v ∧ q' = D.evalFrom q u} := by
    intro v
    induction v with
    | nil =>
      intro q
      ext q'
      simp [NFA.evalFrom]
    | cons c v ih =>
      intro q
      ext q'
      rw [NFA.evalFrom_cons, NFA.stepSet_singleton, NFA.mem_evalFrom_iff_exists]
      constructor
      · rintro ⟨t, ht, hmem⟩
        rw [ih t] at hmem
        obtain ⟨u, hu, rfl⟩ := hmem
        obtain ⟨a, ha, rfl⟩ := ht
        exact ⟨a :: u, by simp [ha, hu], rfl⟩
      · rintro ⟨u, hu, rfl⟩
        cases u with
        | nil => simp at hu
        | cons a u =>
          simp only [List.map_cons, List.cons.injEq] at hu
          refine ⟨D.step q a, ⟨a, hu.1, rfl⟩, ?_⟩
          rw [ih (D.step q a)]
          exact ⟨u, hu.2, rfl⟩
  have hacc : N.accepts = {v : List Δ | ∃ u, u ∈ D.accepts ∧ u.map h = v} := by
    ext v
    rw [NFA.mem_accepts]
    constructor
    · rintro ⟨s, hs, hmem⟩
      have hm : s ∈ N.evalFrom {D.start} v := hmem
      rw [key v D.start] at hm
      obtain ⟨u, hu, rfl⟩ := hm
      exact ⟨u, by simpa [DFA.mem_accepts, DFA.eval] using hs, hu⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨D.eval u, hu, ?_⟩
      show D.eval u ∈ N.evalFrom {D.start} (u.map h)
      rw [key _ D.start]
      exact ⟨u, rfl, rfl⟩
  rw [← hacc]
  exact isRegular_of_nfa N

/-! ## Scanning languages -/

/-- The state of the automaton looking for the first position satisfying `P`,
and testing `R` there. -/
def scanStep (P R : Γ → Bool) : Option Bool → Γ → Option Bool
  | none, x => if P x then some (R x) else none
  | some b, _ => some b

lemma scanStep_absorb (P R : Γ → Bool) (b : Bool) (u : List Γ) :
    u.foldl (scanStep P R) (some b) = some b := by
  induction u with
  | nil => rfl
  | cons x u ih => simpa [scanStep] using ih

lemma scanStep_eval (P R : Γ → Bool) (u : List Γ) :
    u.foldl (scanStep P R) none = (u[u.findIdx P]?).map R := by
  induction u with
  | nil => simp [List.findIdx_nil]
  | cons x u ih =>
    by_cases h : P x
    · simp [List.foldl_cons, scanStep, h, scanStep_absorb, List.findIdx_cons]
    · simp [List.foldl_cons, scanStep, h, ih, List.findIdx_cons]

/-- The language of strings whose first position satisfying `P` exists and
satisfies `R`. -/
lemma isRegular_scan (P R : Γ → Bool) :
    Language.IsRegular {u : List Γ | ∃ x, u[u.findIdx P]? = some x ∧ R x = true} := by
  have h : {u : List Γ | ∃ x, u[u.findIdx P]? = some x ∧ R x = true}
      = {u : List Γ | u.foldl (scanStep P R) none ∈ ({some true} : Set (Option Bool))} := by
    ext u
    simp [scanStep_eval, Option.map_eq_some_iff]
  rw [h]
  exact isRegular_foldl _ _ _

/-- The state of the automaton comparing the first position satisfying `P` with
the first position satisfying `Q`. -/
def leStep (P Q : Γ → Bool) : Option Bool → Γ → Option Bool
  | none, x => if P x then some true else if Q x then some false else none
  | some b, _ => some b

lemma leStep_absorb (P Q : Γ → Bool) (b : Bool) (u : List Γ) :
    u.foldl (leStep P Q) (some b) = some b := by
  induction u with
  | nil => rfl
  | cons x u ih => simpa [leStep] using ih

lemma leStep_eval (P Q : Γ → Bool) (u : List Γ) :
    (u.foldl (leStep P Q) none ∈ ({none, some true} : Set (Option Bool)))
      ↔ u.findIdx P ≤ u.findIdx Q := by
  induction u with
  | nil => simp [List.findIdx_nil]
  | cons x u ih =>
    by_cases hp : P x
    · simp [List.foldl_cons, leStep, hp, leStep_absorb, List.findIdx_cons]
    · by_cases hq : Q x
      · simp [List.foldl_cons, leStep, hp, hq, leStep_absorb, List.findIdx_cons]
      · simpa [List.foldl_cons, leStep, hp, hq, List.findIdx_cons] using ih

/-- The language of strings in which the first position satisfying `P` is not
after the first position satisfying `Q`. -/
lemma isRegular_findIdx_le (P Q : Γ → Bool) :
    Language.IsRegular {u : List Γ | u.findIdx P ≤ u.findIdx Q} := by
  have h : {u : List Γ | u.findIdx P ≤ u.findIdx Q}
      = {u : List Γ | u.foldl (leStep P Q) none ∈ ({none, some true} : Set (Option Bool))} := by
    ext u; exact (leStep_eval P Q u).symm
  rw [h]
  exact isRegular_foldl _ _ _

/-- The state of the automaton counting the occurrences of `P`, capped at
two. -/
def cntStep (P : Γ → Bool) : Fin 3 → Γ → Fin 3 :=
  fun s x => if P x then ⟨min (s.val + 1) 2, by omega⟩ else s

lemma cntStep_eval (P : Γ → Bool) (u : List Γ) (s : Fin 3) :
    (u.foldl (cntStep P) s).val = min (s.val + u.countP P) 2 := by
  induction u generalizing s with
  | nil => simp [List.countP_nil]; omega
  | cons x u ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    by_cases h : P x
    · simp [cntStep, h]
      omega
    · simp [cntStep, h]

/-- The language of strings with exactly one position satisfying `P`. -/
lemma isRegular_countP_eq_one (P : Γ → Bool) :
    Language.IsRegular {u : List Γ | u.countP P = 1} := by
  have h : {u : List Γ | u.countP P = 1}
      = {u : List Γ | u.foldl (cntStep P) ⟨0, by omega⟩ ∈ {s : Fin 3 | s.val = 1}} := by
    ext u
    simp only [Set.mem_setOf_eq, cntStep_eval]
    omega
  rw [h]
  exact isRegular_foldl _ _ _

/-! ## Exactly one occurrence -/

/-- Having exactly one occurrence of `P`, in terms of positions. -/
lemma countP_eq_one_iff (P : Γ → Bool) (u : List Γ) :
    u.countP P = 1 ↔ ∃ p, ∃ hp : p < u.length,
      P u[p] = true ∧ ∀ q, (hq : q < u.length) → P u[q] = true → q = p := by
  induction u with
  | nil => simp [List.countP_nil]
  | cons x u ih =>
    rw [List.countP_cons]
    by_cases hx : P x
    · simp only [hx, if_pos]
      constructor
      · intro h
        have hc : u.countP P = 0 := by omega
        refine ⟨0, by simp, by simpa using hx, ?_⟩
        intro q hq hqP
        rcases q with _ | q
        · rfl
        · exfalso
          have hq' : q < u.length := by simpa using hq
          have hqP' : P u[q] = true := by simpa using hqP
          have : 0 < u.countP P := by
            rw [List.countP_pos_iff]
            exact ⟨u[q], List.getElem_mem hq', hqP'⟩
          omega
      · rintro ⟨p, hp, hpP, hun⟩
        have hc : u.countP P = 0 := by
          by_contra hne
          have hpos : 0 < u.countP P := Nat.pos_of_ne_zero hne
          rw [List.countP_pos_iff] at hpos
          obtain ⟨y, hy, hyP⟩ := hpos
          obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
          have h0 : (0 : ℕ) = p := hun 0 (by simp) (by simpa using hx)
          have hq1 : q + 1 = p := hun (q + 1) (by simpa using hq) (by simpa using hyP)
          omega
        omega
    · simp only [hx, if_false, Bool.false_eq_true, add_zero]
      rw [ih]
      constructor
      · rintro ⟨p, hp, hpP, hun⟩
        refine ⟨p + 1, by simpa using hp, by simpa using hpP, ?_⟩
        intro q hq hqP
        rcases q with _ | q
        · exact absurd (by simpa using hqP) (by simpa using hx)
        · have := hun q (by simpa using hq) (by simpa using hqP)
          omega
      · rintro ⟨p, hp, hpP, hun⟩
        rcases p with _ | p
        · exact absurd (by simpa using hpP) (by simpa using hx)
        · refine ⟨p, by simpa using hp, by simpa using hpP, ?_⟩
          intro q hq hqP
          have := hun (q + 1) (by simpa using hq) (by simpa using hqP)
          omega

/-- The position `p` of `u` exists and satisfies `P`. -/
def MarkedAt (P : Γ → Bool) (u : List Γ) (p : ℕ) : Prop := ∃ x, u[p]? = some x ∧ P x = true

/-- Exactly one position of `u` satisfies `P`. -/
def MarksOnce (P : Γ → Bool) (u : List Γ) : Prop := ∃ p, ∀ q, MarkedAt P u q ↔ q = p

lemma marksOnce_iff_countP (P : Γ → Bool) (u : List Γ) :
    MarksOnce P u ↔ u.countP P = 1 := by
  rw [countP_eq_one_iff]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨x, hx, hPx⟩ := (hp p).2 rfl
    rw [List.getElem?_eq_some_iff] at hx
    obtain ⟨hlt, rfl⟩ := hx
    refine ⟨p, hlt, hPx, ?_⟩
    intro q hq hqP
    exact (hp q).1 ⟨u[q], List.getElem?_eq_getElem hq, hqP⟩
  · rintro ⟨p, hp, hpP, hun⟩
    refine ⟨p, fun q => ?_⟩
    constructor
    · rintro ⟨x, hx, hPx⟩
      rw [List.getElem?_eq_some_iff] at hx
      obtain ⟨hlt, rfl⟩ := hx
      exact hun q hlt hPx
    · rintro rfl
      exact ⟨u[q], List.getElem?_eq_getElem hp, hpP⟩

lemma findIdx_eq_of_marksOnce {P : Γ → Bool} {u : List Γ} {p : ℕ}
    (h : ∀ q, MarkedAt P u q ↔ q = p) : u.findIdx P = p := by
  obtain ⟨x, hx, hPx⟩ := (h p).2 rfl
  rw [List.getElem?_eq_some_iff] at hx
  obtain ⟨hlt, rfl⟩ := hx
  have hex : ∃ y ∈ u, P y := ⟨u[p], List.getElem_mem hlt, hPx⟩
  have hflt : u.findIdx P < u.length := List.findIdx_lt_length_of_exists hex
  exact (h _).1 ⟨u[u.findIdx P], List.getElem?_eq_getElem hflt, List.findIdx_getElem⟩

lemma marksOnce_lt_length {P : Γ → Bool} {u : List Γ} {p : ℕ}
    (h : ∀ q, MarkedAt P u q ↔ q = p) : p < u.length := by
  obtain ⟨x, hx, _⟩ := (h p).2 rfl
  rw [List.getElem?_eq_some_iff] at hx
  exact hx.1

/-! ## Adding a Boolean component that depends on the position -/

/-- Rebuild a string, handing to each position an extra Boolean that depends on
the position. -/
def markWith {Γ Γ' : Type} (g : Γ → Bool → Γ') (b : ℕ → Bool) (v : List Γ) : List Γ' :=
  v.zipIdx.map (fun z => g z.1 (b z.2))

@[simp] lemma markWith_length {Γ Γ' : Type} (g : Γ → Bool → Γ') (b : ℕ → Bool) (v : List Γ) :
    (markWith g b v).length = v.length := by simp [markWith]

lemma markWith_getElem? {Γ Γ' : Type} (g : Γ → Bool → Γ') (b : ℕ → Bool) (v : List Γ) (q : ℕ) :
    (markWith g b v)[q]? = (v[q]?).map (fun x => g x (b q)) := by
  simp [markWith, Option.map_map, Function.comp_def]

lemma map_markWith {Γ Γ' Γ'' : Type} (g : Γ → Bool → Γ') (b : ℕ → Bool) (v : List Γ)
    (f : Γ' → Γ'') (h : Γ → Γ'') (hgf : ∀ x c, f (g x c) = h x) :
    (markWith g b v).map f = v.map h := by
  apply List.ext_getElem?
  intro q
  simp [markWith_getElem?, Option.map_map, Function.comp_def, hgf]

lemma markedAt_markWith_mark {Γ Γ' : Type} (g : Γ → Bool → Γ') (b : ℕ → Bool) (v : List Γ)
    (Q : Γ' → Bool) (hQ : ∀ x c, Q (g x c) = c) (q : ℕ) :
    MarkedAt Q (markWith g b v) q ↔ (q < v.length ∧ b q = true) := by
  simp only [MarkedAt, markWith_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, hQy⟩
    rw [List.getElem?_eq_some_iff] at hx
    exact ⟨hx.1, by rwa [hQ] at hQy⟩
  · rintro ⟨hlt, hb⟩
    exact ⟨g v[q] (b q), ⟨v[q], List.getElem?_eq_getElem hlt, rfl⟩, by rw [hQ]; exact hb⟩

lemma markedAt_markWith_copy {Γ Γ' : Type} (g : Γ → Bool → Γ') (b : ℕ → Bool) (v : List Γ)
    (Q : Γ' → Bool) (R : Γ → Bool) (hQ : ∀ x c, Q (g x c) = R x) (q : ℕ) :
    MarkedAt Q (markWith g b v) q ↔ MarkedAt R v q := by
  simp only [MarkedAt, markWith_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, hQy⟩
    exact ⟨x, hx, by rwa [hQ] at hQy⟩
  · rintro ⟨x, hx, hRx⟩
    exact ⟨g x (b q), ⟨x, hx, rfl⟩, by rw [hQ]; exact hRx⟩

/-- Transporting the marked positions along a letter-to-letter map. -/
lemma markedAt_map {f : Γ → Δ} {P : Γ → Bool} {Q : Δ → Bool} (h : ∀ x, P x = Q (f x))
    (u : List Γ) (q : ℕ) : MarkedAt P u q ↔ MarkedAt Q (u.map f) q := by
  simp only [MarkedAt, List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨x, hx, hPx⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by rw [← h]; exact hPx⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, hQy⟩
    exact ⟨x, hx, by rw [h]; exact hQy⟩

lemma isRegular_marksOnce (P : Γ → Bool) :
    Language.IsRegular {u : List Γ | MarksOnce P u} := by
  have h : {u : List Γ | MarksOnce P u} = {u : List Γ | u.countP P = 1} := by
    ext u; exact marksOnce_iff_countP P u
  rw [h]
  exact isRegular_countP_eq_one P

/-- The language consisting of the empty word only is regular. -/
lemma isRegular_eq_nil : Language.IsRegular {u : List Γ | u = []} := by
  have h := isRegular_foldl (Γ := Γ) (fun (_ : Bool) _ => true) false {false}
  refine isRegular_of_eq h (fun u => ?_)
  constructor
  · rintro rfl
    show List.foldl (fun (_ : Bool) (_ : Γ) => true) false [] ∈ ({false} : Set Bool)
    simp
  · intro hu
    cases u with
    | nil => rfl
    | cons a u =>
      exfalso
      have : List.foldl (fun (_ : Bool) (_ : Γ) => true) false (a :: u) = true := by
        simp only [List.foldl_cons]
        clear hu
        induction u with
        | nil => rfl
        | cons b u ih => simpa using ih
      have hu' : List.foldl (fun (_ : Bool) (_ : Γ) => true) false (a :: u) ∈ ({false} : Set Bool) :=
        hu
      rw [this] at hu'
      simp at hu'

/-! ## Conditions on every letter, and finite unions -/

/-- A language defined by a condition on every letter is regular. -/
lemma isRegular_all (P : Γ → Bool) :
    Language.IsRegular {u : List Γ | ∀ c ∈ u, P c = true} := by
  have key : ∀ (u : List Γ) (b : Bool),
      (u.foldl (fun b c => b && P c) b = true) ↔ (b = true ∧ ∀ c ∈ u, P c = true) := by
    intro u
    induction u with
    | nil => intro b; simp
    | cons c u ih =>
        intro b
        rw [List.foldl_cons, ih]
        simp only [Bool.and_eq_true, List.mem_cons]
        constructor
        · rintro ⟨⟨hb, hc⟩, h⟩
          exact ⟨hb, by rintro x (rfl | hx); exacts [hc, h x hx]⟩
        · rintro ⟨hb, h⟩
          exact ⟨⟨hb, h c (Or.inl rfl)⟩, fun x hx => h x (Or.inr hx)⟩
  refine isRegular_of_eq (isRegular_foldl (Γ := Γ) (fun b c => b && P c) true {true}) ?_
  intro u
  show (∀ c ∈ u, P c = true) ↔ u.foldl (fun b c => b && P c) true ∈ ({true} : Set Bool)
  rw [Set.mem_singleton_iff, key u true]
  simp

/-- Regularity of a finite union. -/
lemma isRegular_exists_finite {ι : Type} [Finite ι] (L : ι → Language Γ)
    (h : ∀ x, (L x).IsRegular) : Language.IsRegular {u : List Γ | ∃ x, u ∈ L x} := by
  letI : Fintype ι := Fintype.ofFinite ι
  have hall := isRegular_forall_list (fun x : ι => {u : List Γ | u ∉ L x})
    (Finset.univ : Finset ι).toList (fun x _ => isRegular_not (h x))
  refine isRegular_of_eq (isRegular_not hall) ?_
  intro u
  show (∃ x, u ∈ L x) ↔ ¬ (∀ x ∈ (Finset.univ : Finset ι).toList, u ∉ L x)
  constructor
  · rintro ⟨x, hx⟩ h
    exact h x (by simp) hx
  · intro h
    by_contra hc
    exact h fun x _ hx => hc ⟨x, hx⟩

end RegAut
end Lax916827Proofs.Transducers
