/- Lemma `lem:decide-if-length-preserving` of *Transducers* (M. Bojańczyk): one can decide whether
the relation described by a code is length preserving.

The decision procedure enumerates all transition sequences of length at most
`3n`, where `n` bounds the number of states of the coded automaton, and checks
that every accepting one is balanced (output and input of the same length).  The
correctness of this bound is a pumping argument, carried out in
`allBalanced_of_short` below with the help of `RequestProject/PartB/PathComb.lean`.
-/
import Lax132576Proofs.Source.PartB.Codes
import Lax132576Proofs.Source.PartB.PathComb
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace LenDec

open LabAut

/-- The type of coded transitions. -/
abbrev Tr := ℕ × List ℕ × List ℕ × ℕ

/-! ## The balance of a transition sequence -/

/-- The total length of the outputs of a transition sequence. -/
def dOut (ts : List Tr) : ℕ := ts.foldr (fun t s => t.2.2.1.length + s) 0

/-- The total length of the inputs of a transition sequence. -/
def dIn (ts : List Tr) : ℕ := ts.foldr (fun t s => t.2.1.length + s) 0

@[simp] lemma dOut_nil : dOut [] = 0 := rfl
@[simp] lemma dIn_nil : dIn [] = 0 := rfl

@[simp] lemma dOut_cons (t : Tr) (ts : List Tr) : dOut (t :: ts) = t.2.2.1.length + dOut ts := rfl
@[simp] lemma dIn_cons (t : Tr) (ts : List Tr) : dIn (t :: ts) = t.2.1.length + dIn ts := rfl

lemma dOut_eq (ts : List Tr) : dOut ts = (NFAO.outputOf ts).length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [ih]

lemma dIn_eq (ts : List Tr) : dIn ts = (inputOf ts).length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [ih]

lemma dOut_append (ts ts' : List Tr) : dOut (ts ++ ts') = dOut ts + dOut ts' := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]; omega

lemma dIn_append (ts ts' : List Tr) : dIn (ts ++ ts') = dIn ts + dIn ts' := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]; omega

/-! ## The pumping argument -/

/-- A list containing all states of the automaton described by a code that can
occur on an accepting path. -/
def stateList (c : RelCode) : List ℕ := c.2.1 ++ c.1.map (fun t => t.2.2.2)

lemma stateList_length (c : RelCode) : (stateList c).length = c.2.1.length + c.1.length := by
  simp [stateList]

lemma target_mem_stateList (c : RelCode) : ∀ t ∈ (codeAut c).δ, (t.2.2.2 : ℕ) ∈ stateList c := by
  intro t ht
  have : t ∈ c.1 := ht
  simp only [stateList, List.mem_append, List.mem_map]
  exact Or.inr ⟨t, this, rfl⟩

lemma init_mem_stateList (c : RelCode) : ∀ q ∈ (codeAut c).init, q ∈ stateList c := by
  intro q hq
  have : q ∈ c.2.1 := hq
  simp [stateList, this]

/-- If all accepting paths of length at most `3n` are balanced, where `n` is the
number of states, then all accepting paths are balanced. -/
lemma allBalanced_of_short (c : RelCode)
    (H : ∀ ts, (codeAut c).Accepting ts → ts.length ≤ 3 * (stateList c).length →
      dOut ts = dIn ts) :
    ∀ ts, (codeAut c).Accepting ts → dOut ts = dIn ts := by
  set M := codeAut c with hM
  set S := stateList c with hS'
  have hS : ∀ t ∈ M.δ, (t.2.2.2 : ℕ) ∈ S := target_mem_stateList c
  intro ts
  generalize hn : ts.length = N
  induction N using Nat.strong_induction_on generalizing ts with
  | _ N ih =>
    intro hacc
    by_cases hshort : ts.length ≤ 3 * S.length
    · exact H ts hacc hshort
    push_neg at hshort
    obtain ⟨q₀, hq₀, p, hp, hpath⟩ := hacc
    have hq₀S : q₀ ∈ S := init_mem_stateList c q₀ hq₀
    have hle : S.length ≤ ts.length := by omega
    obtain ⟨ts₁, ts₂, ts₃, r, hsplit, hne, hlen₂, h₁, h₂, h₃⟩ :=
      Path.small_loop S hS hpath hq₀S hle
    have hrS : r ∈ S := Path.target_mem S hS h₁ hq₀S
    obtain ⟨u, hu, hulen⟩ := Path.exists_short S hS h₁ hq₀S
    obtain ⟨v, hv, hvlen⟩ := Path.exists_short S hS h₃ hrS
    -- `ts₁ ++ ts₃` is a shorter accepting path
    have hacc13 : M.Accepting (ts₁ ++ ts₃) := ⟨q₀, hq₀, p, hp, h₁.append h₃⟩
    have hlen13 : (ts₁ ++ ts₃).length < ts.length := by
      have h2 : ts₂.length ≠ 0 := by simpa using hne
      subst hsplit
      simp only [List.length_append]
      omega
    have e13 : dOut (ts₁ ++ ts₃) = dIn (ts₁ ++ ts₃) :=
      ih (ts₁ ++ ts₃).length (by omega) (ts₁ ++ ts₃) rfl hacc13
    -- `u ++ v` and `u ++ ts₂ ++ v` are short accepting paths
    have haccuv : M.Accepting (u ++ v) := ⟨q₀, hq₀, p, hp, hu.append hv⟩
    have haccu2v : M.Accepting (u ++ ts₂ ++ v) :=
      ⟨q₀, hq₀, p, hp, (hu.append h₂).append hv⟩
    have euv : dOut (u ++ v) = dIn (u ++ v) := by
      refine H _ haccuv ?_
      simp only [List.length_append]
      omega
    have eu2v : dOut (u ++ ts₂ ++ v) = dIn (u ++ ts₂ ++ v) := by
      refine H _ haccu2v ?_
      simp only [List.length_append]
      omega
    rw [dOut_append, dIn_append] at e13 euv
    rw [dOut_append, dOut_append, dIn_append, dIn_append] at eu2v
    subst hsplit
    rw [dOut_append, dOut_append, dIn_append, dIn_append]
    omega

/-- The length preservation property, expressed on paths. -/
lemma lengthPreserving_iff_balanced (c : RelCode) :
    (∀ w v, codeRel c w v → v.length = w.length) ↔
      ∀ ts, (codeAut c).Accepting ts → dOut ts = dIn ts := by
  constructor
  · intro h ts hacc
    have : codeRel c (inputOf ts) (NFAO.outputOf ts) := ⟨ts, hacc, rfl, rfl⟩
    rw [dOut_eq, dIn_eq]
    exact h _ _ this
  · rintro h w v ⟨ts, hacc, rfl, rfl⟩
    rw [← dOut_eq, ← dIn_eq]
    exact h ts hacc

/-! ## Boolean helpers

These are `foldr`-based versions of `List.any`, `List.all` and list membership;
they are used so that the decision procedure below is manifestly built from
primitive recursive combinators. -/

/-- `foldr`-based existential quantifier over a list. -/
def anyB {α : Type} (l : List α) (p : α → Bool) : Bool := l.foldr (fun x b => p x || b) false

/-- `foldr`-based universal quantifier over a list. -/
def allB {α : Type} (l : List α) (p : α → Bool) : Bool := l.foldr (fun x b => p x && b) true

lemma anyB_iff {α : Type} (l : List α) (p : α → Bool) :
    anyB l p = true ↔ ∃ x ∈ l, p x = true := by
  induction l with
  | nil => simp [anyB]
  | cons x l ih =>
      simp only [anyB, List.foldr_cons, Bool.or_eq_true, List.mem_cons] at *
      rw [ih]
      constructor
      · rintro (h | ⟨y, hy, hp⟩)
        exacts [⟨x, Or.inl rfl, h⟩, ⟨y, Or.inr hy, hp⟩]
      · rintro ⟨y, rfl | hy, hp⟩
        exacts [Or.inl hp, Or.inr ⟨y, hy, hp⟩]

lemma allB_iff {α : Type} (l : List α) (p : α → Bool) :
    allB l p = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [allB]
  | cons x l ih => simp only [allB, List.foldr_cons, Bool.and_eq_true] at *; simp [ih]

/-- `foldr`-based list membership test. -/
def memB {α : Type} [DecidableEq α] (l : List α) (x : α) : Bool :=
  anyB l (fun y => decide (y = x))

lemma memB_iff {α : Type} [DecidableEq α] (l : List α) (x : α) : memB l x = true ↔ x ∈ l := by
  rw [memB, anyB_iff]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [decide_eq_true_eq] at h
    exact h ▸ hy
  · intro h
    exact ⟨x, h, by simp⟩

/-! ## The decision procedure -/

/-- One step of the run of a coded automaton on a transition sequence. -/
def stepO (L : List Tr) (o : Option ℕ) (t : Tr) : Option ℕ :=
  o.bind (fun q => bif decide (t.1 = q) && memB L t then some t.2.2.2 else none)

/-- The state reached by following a transition sequence from `q`, if the
sequence is a genuine path. -/
def runO (L : List Tr) (q : ℕ) (ts : List Tr) : Option ℕ := ts.foldl (stepO L) (some q)

lemma foldl_stepO_none (L : List Tr) (ts : List Tr) :
    ts.foldl (stepO L) none = none := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa [stepO] using ih

lemma runO_iff (L : List Tr) (M : NFAO ℕ ℕ ℕ) (hM : ∀ t, t ∈ M.δ ↔ t ∈ L) :
    ∀ (ts : List Tr) (q p : ℕ), runO L q ts = some p ↔ M.Path q ts p := by
  intro ts
  induction ts with
  | nil =>
      intro q p
      constructor
      · intro h; cases (Option.some_inj.1 h); exact Path.nil q
      · intro h; rw [Path.eq_of_nil h]; rfl
  | cons t ts ih =>
      intro q p
      by_cases hcond : t.1 = q ∧ t ∈ L
      · have hmemB : memB L t = true := (memB_iff L t).2 hcond.2
        have hstep : stepO L (some q) t = some t.2.2.2 := by
          simp [stepO, hcond.1, hmemB]
        rw [runO, List.foldl_cons, hstep]
        rw [show ts.foldl (stepO L) (some t.2.2.2) = runO L t.2.2.2 ts from rfl, ih]
        constructor
        · intro h
          have ht : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : Tr) ∈ M.δ := (hM t).2 hcond.2
          rw [← hcond.1]
          exact Path.cons ht h
        · intro h
          exact (Path.cons_inv h).2.2
      · have hstep : stepO L (some q) t = none := by
          rcases Classical.em (t.1 = q) with h1 | h1
          · have h2 : t ∉ L := fun hc => hcond ⟨h1, hc⟩
            have hmemB : memB L t = false :=
              Bool.eq_false_iff.2 (fun hc => h2 ((memB_iff L t).1 hc))
            simp [stepO, h1, hmemB]
          · simp [stepO, h1]
        rw [runO, List.foldl_cons, hstep, foldl_stepO_none]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h
          obtain ⟨h1, h2, _⟩ := Path.cons_inv h
          exact absurd ⟨h1, (hM t).1 h2⟩ hcond

/-- The boolean test for a transition sequence being an accepting path. -/
def acceptB (c : RelCode) (ts : List Tr) : Bool :=
  anyB c.2.1 (fun q => ((runO c.1 q ts).map (fun p => memB c.2.2 p)).getD false)

lemma acceptB_iff (c : RelCode) (ts : List Tr) :
    acceptB c ts = true ↔ (codeAut c).Accepting ts := by
  have hM : ∀ t, t ∈ (codeAut c).δ ↔ t ∈ c.1 := fun t => Iff.rfl
  constructor
  · intro h
    obtain ⟨q, hq, hq'⟩ := (anyB_iff _ _).1 h
    rcases hrun : runO c.1 q ts with _ | p
    · rw [hrun] at hq'; simp at hq'
    · rw [hrun] at hq'
      simp only [Option.map_some, Option.getD_some, memB_iff] at hq'
      exact ⟨q, hq, p, hq', (runO_iff c.1 (codeAut c) hM ts q p).1 hrun⟩
  · rintro ⟨q, hq, p, hp, hpath⟩
    refine (anyB_iff _ _).2 ⟨q, hq, ?_⟩
    rw [(runO_iff c.1 (codeAut c) hM ts q p).2 hpath]
    simpa [memB_iff] using hp

/-- The boolean test for a transition sequence being balanced. -/
def balB (ts : List Tr) : Bool := decide (dOut ts = dIn ts)

/-- All transition sequences of length at most `k` over the transitions `L`. -/
def seqsUpto (L : List Tr) (k : ℕ) : List (List Tr) :=
  Nat.rec [[]] (fun _ ih => [] :: L.flatMap (fun t => ih.map (fun ts => t :: ts))) k

@[simp] lemma seqsUpto_zero (L : List Tr) : seqsUpto L 0 = [[]] := rfl

@[simp] lemma seqsUpto_succ (L : List Tr) (k : ℕ) :
    seqsUpto L (k + 1) = [] :: L.flatMap (fun t => (seqsUpto L k).map (fun ts => t :: ts)) := rfl

lemma mem_seqsUpto (L : List Tr) (k : ℕ) (ts : List Tr) :
    ts ∈ seqsUpto L k ↔ ts.length ≤ k ∧ ∀ t ∈ ts, t ∈ L := by
  induction k generalizing ts with
  | zero =>
      simp only [seqsUpto_zero, List.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact h
  | succ k ih =>
      constructor
      · intro h
        simp only [seqsUpto_succ, List.mem_cons, List.mem_flatMap, List.mem_map] at h
        rcases h with rfl | ⟨t, htL, rest, hrest, rfl⟩
        · simp
        · obtain ⟨h1, h2⟩ := (ih rest).1 hrest
          refine ⟨by simpa using h1, ?_⟩
          intro s hs
          rcases List.mem_cons.1 hs with rfl | hs'
          · exact htL
          · exact h2 s hs'
      · rintro ⟨h1, h2⟩
        simp only [seqsUpto_succ, List.mem_cons, List.mem_flatMap, List.mem_map]
        match ts with
        | [] => exact Or.inl rfl
        | t :: rest =>
            refine Or.inr ⟨t, h2 t (by simp), rest, ?_, rfl⟩
            exact (ih rest).2 ⟨by simpa using h1, fun s hs => h2 s (by simp [hs])⟩

/-- The decision procedure for Lemma `lem:decide-if-length-preserving`. -/
def lenDec (c : RelCode) : Bool :=
  allB (seqsUpto c.1 (3 * (c.2.1.length + c.1.length)))
    (fun ts => !acceptB c ts || balB ts)

lemma lenDec_iff (c : RelCode) :
    lenDec c = true ↔ ∀ w v, codeRel c w v → v.length = w.length := by
  rw [lengthPreserving_iff_balanced]
  constructor
  · intro h
    refine allBalanced_of_short c ?_
    intro ts hacc hlen
    have hmem : ts ∈ seqsUpto c.1 (3 * (c.2.1.length + c.1.length)) := by
      refine (mem_seqsUpto _ _ _).2 ⟨by rwa [stateList_length] at hlen, ?_⟩
      obtain ⟨q, -, p, -, hpath⟩ := hacc
      exact fun t ht => Path.mem_delta hpath t ht
    have := (allB_iff _ _).1 h ts hmem
    rw [(acceptB_iff c ts).2 hacc] at this
    simpa [balB] using this
  · intro h
    refine (allB_iff _ _).2 ?_
    intro ts _
    by_cases hacc : acceptB c ts = true
    · have := h ts ((acceptB_iff c ts).1 hacc)
      simp [hacc, balB, this]
    · simp only [Bool.not_eq_true] at hacc
      simp [hacc]

/-! ## Computability of the decision procedure -/

/-- Equality tests are primitive recursive.  (A wrapper around `Primrec.eq`
which produces the `Decidable` instance coming from `DecidableEq`.) -/
lemma primrec_decEq {α : Type} [Primcodable α] [DecidableEq α] {γ : Type} [Primcodable γ]
    {f g : γ → α} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => decide (f x = g x)) := by
  obtain ⟨_, h⟩ := Primrec.eq.comp hf hg
  exact h.of_eq (fun x => by by_cases hx : f x = g x <;> simp [hx])

lemma primrec_memB {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec₂ (fun (l : List α) (x : α) => memB l x) := by
  show Primrec fun z : List α × α => List.foldr (fun y b => decide (y = z.2) || b) false z.1
  refine (Primrec.list_foldr (h := fun z q => (decide (q.1 = z.2) || q.2))
    Primrec.fst (Primrec.const false) ?_).of_eq (fun _ => rfl)
  show Primrec fun w : (List α × α) × (α × Bool) => (decide (w.2.1 = w.1.2) || w.2.2)
  exact Primrec.or.comp
    (primrec_decEq (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp Primrec.snd)

lemma primrec_dOut : Primrec dOut := by
  refine (Primrec.list_foldr (h := fun _ q => q.1.2.2.1.length + q.2)
    Primrec.id (Primrec.const 0) ?_).of_eq (fun _ => rfl)
  show Primrec fun w : List Tr × (Tr × ℕ) => (w.2.1.2.2.1.length + w.2.2)
  exact Primrec.nat_add.comp
    (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.fst.comp Primrec.snd)))))
    (Primrec.snd.comp Primrec.snd)

lemma primrec_dIn : Primrec dIn := by
  refine (Primrec.list_foldr (h := fun _ q => q.1.2.1.length + q.2)
    Primrec.id (Primrec.const 0) ?_).of_eq (fun _ => rfl)
  show Primrec fun w : List Tr × (Tr × ℕ) => (w.2.1.2.1.length + w.2.2)
  exact Primrec.nat_add.comp
    (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
    (Primrec.snd.comp Primrec.snd)

lemma primrec_balB : Primrec balB := primrec_decEq primrec_dOut primrec_dIn

lemma primrec_stepO : Primrec (fun z : List Tr × Option ℕ × Tr => stepO z.1 z.2.1 z.2.2) := by
  refine Primrec.option_bind (Primrec.fst.comp Primrec.snd) ?_
  show Primrec fun w : (List Tr × Option ℕ × Tr) × ℕ =>
    (bif decide (w.1.2.2.1 = w.2) && memB w.1.1 w.1.2.2 then some w.1.2.2.2.2.2 else none)
  have ht : Primrec (fun w : (List Tr × Option ℕ × Tr) × ℕ => w.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  refine Primrec.cond (Primrec.and.comp ?_ ?_) ?_ (Primrec.const none)
  · exact primrec_decEq (Primrec.fst.comp ht) Primrec.snd
  · exact primrec_memB.comp (Primrec.fst.comp Primrec.fst) ht
  · exact Primrec.option_some.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ht)))

lemma primrec_runO : Primrec (fun z : (List Tr × ℕ) × List Tr => runO z.1.1 z.1.2 z.2) := by
  refine (Primrec.list_foldl (h := fun z q => stepO z.1.1 q.1 q.2) Primrec.snd
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)) ?_).of_eq (fun _ => rfl)
  show Primrec fun w : ((List Tr × ℕ) × List Tr) × (Option ℕ × Tr) =>
    stepO w.1.1.1 w.2.1 w.2.2
  exact primrec_stepO.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

lemma primrec_acceptB : Primrec (fun z : RelCode × List Tr => acceptB z.1 z.2) := by
  refine (Primrec.list_foldr
    (h := fun z q => (((runO z.1.1 q.1 z.2).map (fun p => memB z.1.2.2 p)).getD false || q.2))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const false) ?_).of_eq
    (fun _ => rfl)
  show Primrec fun w : (RelCode × List Tr) × (ℕ × Bool) =>
    (((runO w.1.1.1 w.2.1 w.1.2).map (fun p => memB w.1.1.2.2 p)).getD false || w.2.2)
  refine Primrec.or.comp ?_ (Primrec.snd.comp Primrec.snd)
  refine Primrec.option_getD.comp ?_ (Primrec.const false)
  refine Primrec.option_map ?_ ?_
  · exact primrec_runO.comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
  · show Primrec fun v : ((RelCode × List Tr) × (ℕ × Bool)) × ℕ => memB v.1.1.1.2.2 v.2
    exact primrec_memB.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd

lemma primrec_seqsUpto : Primrec₂ (fun (L : List Tr) (k : ℕ) => seqsUpto L k) := by
  refine Primrec.nat_rec (f := fun _ : List Tr => ([[]] : List (List Tr)))
    (g := fun L p => ([] : List Tr) :: L.flatMap (fun t => p.2.map (fun ts => t :: ts)))
    (Primrec.const _) ?_
  show Primrec fun z : List Tr × (ℕ × List (List Tr)) =>
    ([] : List Tr) :: z.1.flatMap (fun t => z.2.2.map (fun ts => t :: ts))
  refine Primrec.list_cons.comp (Primrec.const ([] : List Tr)) ?_
  refine Primrec.list_flatMap Primrec.fst ?_
  show Primrec fun w : (List Tr × (ℕ × List (List Tr))) × Tr =>
    w.1.2.2.map (fun ts => w.2 :: ts)
  refine Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) ?_
  show Primrec fun v : ((List Tr × (ℕ × List (List Tr))) × Tr) × List Tr => v.1.2 :: v.2
  exact Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd

set_option maxHeartbeats 1000000 in
lemma primrec_lenDec : Primrec lenDec := by
  have hseq : Primrec (fun c : RelCode => seqsUpto c.1 (3 * (c.2.1.length + c.1.length))) :=
    primrec_seqsUpto.comp Primrec.fst
      (Primrec.nat_mul.comp (Primrec.const 3)
        (Primrec.nat_add.comp
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.list_length.comp Primrec.fst)))
  refine (Primrec.list_foldr (h := fun c q => ((!acceptB c q.1 || balB q.1) && q.2))
    hseq (Primrec.const true) ?_).of_eq (fun _ => rfl)
  show Primrec fun w : RelCode × (List Tr × Bool) =>
    ((!acceptB w.1 w.2.1 || balB w.2.1) && w.2.2)
  exact Primrec.and.comp
    (Primrec.or.comp
      (Primrec.not.comp (primrec_acceptB.comp
        (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))))
      (primrec_balB.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd)

lemma computable_lenDec : Computable lenDec := primrec_lenDec.to_comp

end LenDec
end Lax132576Proofs.Transducers
