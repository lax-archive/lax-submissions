/-
Explicit enumeration of the runs of a *letter-atomic* automaton with labelled
transitions.

If every transition of an automaton reads exactly one letter, then a run over an
input string `w` has exactly `|w|` transitions, and the runs can be listed by a
simple recursion on `w`.  This file develops that enumeration and the facts that
the constructions of Section *Rational relations and weighted automata* need:

* `RunList.runs δ q w` lists the runs from the state `q` over the string `w`;
* `RunList.mem_runs` identifies its members with the paths of the automaton;
* `RunList.runs_nodup` says that the list has no repetitions, provided the list
  of transitions has none;
* `RunList.accRuns` and `RunList.allRuns` restrict to the accepting runs, and
  `RunList.acceptingOn_eq` identifies the set of accepting runs of the automaton
  over a *nonempty* string with the set of members of `allRuns`.

The restriction to nonempty strings is needed and harmless: over the empty
string the only candidate run is the empty one, and the automaton has an
accepting run over the empty string exactly when some state is both initial and
final -- a single run, however many such states there are, so the enumeration
`allRuns` (which lists one entry per initial state) would over-count.  All the
automata to which this file is applied have no state that is both initial and
final.

Since the labels of the transitions are arbitrary, the file applies both to nfas
with output (labels are output strings) and to weighted automata (labels are
rational numbers).
-/
import Lax132576Proofs.Source.PartB.PathComb
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace RunList

open LabAut

variable {L : Type}

/-- The type of transitions with states and input letters coded by natural
numbers and labels in `L`. -/
abbrev T (L : Type) := ℕ × List ℕ × L × ℕ

/-- Every transition reads exactly one letter. -/
def Atomic (δ : List (T L)) : Prop := ∀ t ∈ δ, ∃ a, t.2.1 = [a]

/-- The state reached by following a transition sequence from a given state. -/
def tgt : ℕ → List (T L) → ℕ
  | q, [] => q
  | _, t :: ts => tgt t.2.2.2 ts

@[simp] lemma tgt_nil (q : ℕ) : tgt q ([] : List (T L)) = q := rfl

@[simp] lemma tgt_cons (q : ℕ) (t : T L) (ts : List (T L)) :
    tgt q (t :: ts) = tgt t.2.2.2 ts := rfl

lemma tgt_eq_of_path {M : LabAut ℕ L ℕ} {q p : ℕ} {ts : List (T L)}
    (h : M.Path q ts p) : p = tgt q ts := by
  induction h with
  | nil q => rfl
  | cons _ _ ih => simpa using ih

/-- All transition sequences that form a path from `q` reading `w`, in an
automaton all of whose transitions read exactly one letter. -/
def runs (δ : List (T L)) : ℕ → List ℕ → List (List (T L))
  | _, [] => [[]]
  | q, a :: w =>
      δ.flatMap (fun t =>
        if t.1 = q ∧ t.2.1 = [a] then (runs δ t.2.2.2 w).map (fun ts => t :: ts) else [])

@[simp] lemma runs_nil (δ : List (T L)) (q : ℕ) : runs δ q [] = [[]] := rfl

lemma runs_cons (δ : List (T L)) (q a : ℕ) (w : List ℕ) :
    runs δ q (a :: w) =
      δ.flatMap (fun t =>
        if t.1 = q ∧ t.2.1 = [a] then (runs δ t.2.2.2 w).map (fun ts => t :: ts) else []) :=
  rfl

lemma length_of_mem_runs {δ : List (T L)} :
    ∀ {q : ℕ} {w : List ℕ} {ts : List (T L)}, ts ∈ runs δ q w → ts.length = w.length := by
  intro q w
  induction w generalizing q with
  | nil => intro ts h; simp at h; simp [h]
  | cons a w ih =>
      intro ts h
      rw [runs_cons, List.mem_flatMap] at h
      obtain ⟨t, -, ht⟩ := h
      by_cases hc : t.1 = q ∧ t.2.1 = [a]
      · rw [if_pos hc, List.mem_map] at ht
        obtain ⟨ts', hts', rfl⟩ := ht
        simp [ih hts']
      · rw [if_neg hc] at ht; simp at ht

lemma mem_of_mem_runs {δ : List (T L)} :
    ∀ {q : ℕ} {w : List ℕ} {ts : List (T L)}, ts ∈ runs δ q w → ∀ t ∈ ts, t ∈ δ := by
  intro q w
  induction w generalizing q with
  | nil => intro ts h; simp at h; simp [h]
  | cons a w ih =>
      intro ts h
      rw [runs_cons, List.mem_flatMap] at h
      obtain ⟨t, htδ, ht⟩ := h
      by_cases hc : t.1 = q ∧ t.2.1 = [a]
      · rw [if_pos hc, List.mem_map] at ht
        obtain ⟨ts', hts', rfl⟩ := ht
        intro s hs
        rcases List.mem_cons.1 hs with rfl | hs'
        · exact htδ
        · exact ih hts' s hs'
      · rw [if_neg hc] at ht; simp at ht

/-- The members of `runs δ q w` are exactly the paths from `q` reading `w`. -/
lemma mem_runs {M : LabAut ℕ L ℕ} {δ : List (T L)} (hδ : ∀ t, t ∈ M.δ ↔ t ∈ δ)
    (hat : Atomic δ) :
    ∀ {q : ℕ} {w : List ℕ} {ts : List (T L)},
      ts ∈ runs δ q w ↔ (M.Path q ts (tgt q ts) ∧ inputOf ts = w) := by
  intro q w
  induction w generalizing q with
  | nil =>
      intro ts
      simp only [runs_nil, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨Path.nil q, rfl⟩
      · rintro ⟨hp, hin⟩
        rcases ts with _ | ⟨t, ts'⟩
        · rfl
        · obtain ⟨-, htδ, -⟩ := Path.cons_inv hp
          obtain ⟨a, ha⟩ := hat t ((hδ t).1 htδ)
          rw [inputOf_cons, ha] at hin
          simp at hin
  | cons a w ih =>
      intro ts
      rw [runs_cons, List.mem_flatMap]
      constructor
      · rintro ⟨t, htδ, ht⟩
        by_cases hc : t.1 = q ∧ t.2.1 = [a]
        · rw [if_pos hc, List.mem_map] at ht
          obtain ⟨ts', hts', rfl⟩ := ht
          obtain ⟨hp, hin⟩ := ih.1 hts'
          refine ⟨?_, by simp [hin, hc.2]⟩
          have htM : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : T L) ∈ M.δ := (hδ t).2 htδ
          rw [tgt_cons]
          rw [← hc.1]
          exact Path.cons htM hp
        · rw [if_neg hc] at ht; simp at ht
      · rintro ⟨hp, hin⟩
        rcases ts with _ | ⟨t, ts'⟩
        · simp at hin
        obtain ⟨hq, htδ, hp'⟩ := Path.cons_inv hp
        obtain ⟨b, hb⟩ := hat t ((hδ t).1 htδ)
        rw [inputOf_cons, hb] at hin
        have hba : b = a := by simpa using congrArg (List.head? ·) hin
        have hinw : inputOf ts' = w := by
          rw [hba] at hin; simpa using hin
        refine ⟨t, (hδ t).1 htδ, ?_⟩
        rw [if_pos ⟨hq, by rw [hb, hba]⟩, List.mem_map]
        exact ⟨ts', ih.2 ⟨hp', hinw⟩, rfl⟩

lemma runs_head {δ : List (T L)} {q a : ℕ} {w : List ℕ} {t : T L} {ts : List (T L)}
    (h : (t :: ts) ∈ runs δ q (a :: w)) : t.1 = q := by
  rw [runs_cons, List.mem_flatMap] at h
  obtain ⟨s, -, hs⟩ := h
  by_cases hc : s.1 = q ∧ s.2.1 = [a]
  · rw [if_pos hc, List.mem_map] at hs
    obtain ⟨ts', -, heq⟩ := hs
    rw [← (List.cons_eq_cons.1 heq).1]
    exact hc.1
  · rw [if_neg hc] at hs; simp at hs

lemma runs_nodup {δ : List (T L)} (hnd : δ.Nodup) :
    ∀ (q : ℕ) (w : List ℕ), (runs δ q w).Nodup := by
  intro q w
  induction w generalizing q with
  | nil => simp
  | cons a w ih =>
      rw [runs_cons]
      refine List.nodup_flatMap.2 ⟨?_, ?_⟩
      · intro t _
        by_cases hc : t.1 = q ∧ t.2.1 = [a]
        · rw [if_pos hc]
          exact (ih t.2.2.2).map (fun _ _ h => (List.cons_eq_cons.1 h).2)
        · rw [if_neg hc]; simp
      refine hnd.imp ?_
      · intro t s hts
        rw [Function.onFun]
        refine List.disjoint_left.2 ?_
        intro us hu hu'
        by_cases hc : t.1 = q ∧ t.2.1 = [a]
        · by_cases hc' : s.1 = q ∧ s.2.1 = [a]
          · rw [if_pos hc, List.mem_map] at hu
            rw [if_pos hc', List.mem_map] at hu'
            obtain ⟨_, -, rfl⟩ := hu
            obtain ⟨_, -, heq⟩ := hu'
            exact hts (List.cons_eq_cons.1 heq).1.symm
          · rw [if_neg hc'] at hu'; simp at hu'
        · rw [if_neg hc] at hu; simp at hu

/-! ## Accepting runs -/

/-- The accepting runs from a given state: those ending in a state of `F`. -/
def accRuns (δ : List (T L)) (F : List ℕ) (q : ℕ) (w : List ℕ) : List (List (T L)) :=
  (runs δ q w).filter (fun ts => decide (tgt q ts ∈ F))

/-- All accepting runs over a string: those starting in a state of `I`. -/
def allRuns (δ : List (T L)) (I F : List ℕ) (w : List ℕ) : List (List (T L)) :=
  I.flatMap (fun q => accRuns δ F q w)

lemma mem_accRuns {δ : List (T L)} {F : List ℕ} {q : ℕ} {w : List ℕ} {ts : List (T L)} :
    ts ∈ accRuns δ F q w ↔ ts ∈ runs δ q w ∧ tgt q ts ∈ F := by
  simp [accRuns, List.mem_filter]

lemma accRuns_nodup {δ : List (T L)} (hnd : δ.Nodup) (F : List ℕ) (q : ℕ) (w : List ℕ) :
    (accRuns δ F q w).Nodup :=
  (runs_nodup hnd q w).filter _

lemma allRuns_nodup {δ : List (T L)} (hnd : δ.Nodup) {I F : List ℕ} (hI : I.Nodup)
    {w : List ℕ} (hw : w ≠ []) : (allRuns δ I F w).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun q _ => accRuns_nodup hnd F q w, hI.imp ?_⟩
  intro p q hpq
  rw [Function.onFun]
  refine List.disjoint_left.2 ?_
  intro ts h h'
  rcases w with _ | ⟨a, w'⟩
  · exact absurd rfl hw
  rcases ts with _ | ⟨t, ts'⟩
  · have := length_of_mem_runs (mem_accRuns.1 h).1
    simp at this
  · exact hpq ((runs_head (mem_accRuns.1 h).1).symm.trans (runs_head (mem_accRuns.1 h').1))

/-- Over a nonempty string, the accepting runs of the automaton are exactly the
members of `allRuns`. -/
lemma acceptingOn_eq {M : LabAut ℕ L ℕ} {δ : List (T L)} {I F : List ℕ}
    (hδ : ∀ t, t ∈ M.δ ↔ t ∈ δ) (hI : ∀ q, q ∈ M.init ↔ q ∈ I)
    (hF : ∀ p, p ∈ M.final ↔ p ∈ F) (hat : Atomic δ) {w : List ℕ} :
    M.acceptingOn w = {ts | ts ∈ allRuns δ I F w} := by
  ext ts
  simp only [acceptingOn, Accepting, Set.mem_setOf_eq, allRuns, List.mem_flatMap]
  constructor
  · rintro ⟨⟨q, hq, p, hp, hpath⟩, hin⟩
    refine ⟨q, (hI q).1 hq, mem_accRuns.2 ⟨(mem_runs hδ hat).2 ⟨?_, hin⟩, ?_⟩⟩
    · rwa [← tgt_eq_of_path hpath]
    · rw [← tgt_eq_of_path hpath]; exact (hF p).1 hp
  · rintro ⟨q, hq, hmem⟩
    obtain ⟨hruns, hfin⟩ := mem_accRuns.1 hmem
    obtain ⟨hpath, hin⟩ := (mem_runs hδ hat).1 hruns
    exact ⟨⟨q, (hI q).2 hq, tgt q ts, (hF _).2 hfin, hpath⟩, hin⟩

/-- A letter-atomic automaton has finitely many accepting runs over every
string. -/
lemma finite_acceptingOn {M : LabAut ℕ L ℕ} {δ : List (T L)} {I F : List ℕ}
    (hδ : ∀ t, t ∈ M.δ ↔ t ∈ δ) (hI : ∀ q, q ∈ M.init ↔ q ∈ I)
    (hF : ∀ p, p ∈ M.final ↔ p ∈ F) (hat : Atomic δ) (w : List ℕ) :
    (M.acceptingOn w).Finite := by
  rw [acceptingOn_eq hδ hI hF hat]
  exact (allRuns δ I F w).finite_toSet

/-- The number of accepting runs over a nonempty string. -/
lemma card_acceptingOn [DecidableEq L] {M : LabAut ℕ L ℕ} {δ : List (T L)} {I F : List ℕ}
    (hδ : ∀ t, t ∈ M.δ ↔ t ∈ δ) (hI : ∀ q, q ∈ M.init ↔ q ∈ I)
    (hF : ∀ p, p ∈ M.final ↔ p ∈ F) (hat : Atomic δ) (hnd : δ.Nodup) (hIn : I.Nodup)
    {w : List ℕ} (hw : w ≠ []) :
    Nat.card (M.acceptingOn w) = (allRuns δ I F w).length := by
  have hnd' := allRuns_nodup hnd hIn hw (F := F)
  rw [acceptingOn_eq hδ hI hF hat, ← List.coe_toFinset, Nat.card_coe_set_eq,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd']

/-- The value of a letter-atomic weighted automaton on a nonempty string is the
sum of the weights of the runs listed by `allRuns`. -/
lemma wEval_eq_sum {M : LabAut ℕ ℚ ℕ} {δ : List (T ℚ)} {I F : List ℕ}
    (hδ : ∀ t, t ∈ M.δ ↔ t ∈ δ) (hI : ∀ q, q ∈ M.init ↔ q ∈ I)
    (hF : ∀ p, p ∈ M.final ↔ p ∈ F) (hat : Atomic δ) (hnd : δ.Nodup) (hIn : I.Nodup)
    {w : List ℕ} (hw : w ≠ []) :
    M.wEval w = ((allRuns δ I F w).map weightOf).sum := by
  have hnd' := allRuns_nodup hnd hIn hw (F := F)
  rw [wEval, acceptingOn_eq hδ hI hF hat, ← List.coe_toFinset, finsum_mem_coe_finset,
    ← List.sum_toFinset _ hnd']

/-! ## Recursion for the accepting runs

The sum of an arbitrary quantity over the accepting runs of a letter-atomic
automaton satisfies a recursion over the input string: the runs over `a :: w`
are obtained from a transition reading `a` followed by a run over `w`.  This is
what makes the value of the product weighted automaton of
`RequestProject/PartB/PairWeighted.lean` computable by induction. -/

lemma filter_flatMap {α β : Type} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun x => (f x).filter p) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filter_append, ih]

lemma filter_map_cons (t : T L) (F : List ℕ) (q : ℕ) (l : List (List (T L))) :
    (l.map (fun ts => t :: ts)).filter (fun ts => decide (tgt q ts ∈ F))
      = (l.filter (fun ts => decide (tgt t.2.2.2 ts ∈ F))).map (fun ts => t :: ts) := by
  induction l with
  | nil => rfl
  | cons u us ih => by_cases h : tgt t.2.2.2 u ∈ F <;> simp [h, ih]

lemma accRuns_nil' (δ : List (T L)) (F : List ℕ) (q : ℕ) :
    accRuns δ F q [] = if q ∈ F then [[]] else [] := by
  rw [accRuns, runs_nil]
  by_cases h : q ∈ F <;> simp [h]

lemma accRuns_cons (δ : List (T L)) (F : List ℕ) (q a : ℕ) (w : List ℕ) :
    accRuns δ F q (a :: w) =
      δ.flatMap (fun t => if t.1 = q ∧ t.2.1 = [a] then
        (accRuns δ F t.2.2.2 w).map (fun ts => t :: ts) else []) := by
  rw [accRuns, runs_cons, filter_flatMap]
  congr 1
  funext t
  by_cases hc : t.1 = q ∧ t.2.1 = [a]
  · rw [if_pos hc, if_pos hc, accRuns, filter_map_cons]
  · rw [if_neg hc, if_neg hc]; rfl

lemma sum_map_flatMap {α β S : Type} [AddCommMonoid S] (l : List α) (f : α → List β)
    (g : β → S) :
    ((l.flatMap f).map g).sum = (l.map (fun x => ((f x).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

lemma length_map_one {α : Type} (l : List α) : (l.map (fun _ => (1 : ℕ))).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
      omega

/-- The recursion satisfied by a sum over the accepting runs. -/
lemma sum_map_accRuns_cons {S : Type} [AddCommMonoid S] (δ : List (T L)) (F : List ℕ)
    (q a : ℕ) (w : List ℕ) (g : List (T L) → S) :
    ((accRuns δ F q (a :: w)).map g).sum
      = (δ.map (fun t => if t.1 = q ∧ t.2.1 = [a] then
          ((accRuns δ F t.2.2.2 w).map (fun ts => g (t :: ts))).sum else 0)).sum := by
  rw [accRuns_cons, sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left (fun t _ => ?_))
  by_cases hc : t.1 = q ∧ t.2.1 = [a]
  · rw [if_pos hc, if_pos hc, List.map_map]; rfl
  · rw [if_neg hc, if_neg hc]; rfl

end RunList
end Lax132576Proofs.Transducers
