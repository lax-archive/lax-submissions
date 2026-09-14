/-
A letter-atomic normal form for codes of nfas with output.

Starting from the atomisation of `RequestProject/PartB/CodeAtom.lean`, in which
every transition reads at most one letter, this file builds a code `normCode c`
in which every transition reads *exactly* one letter: a transition of
`normCode c` is a short path of the atomised code that reads one letter (its
ε-transitions being absorbed into it), and a run is completed by a transition
that also absorbs the ε-transitions following the last letter and jumps to a
fresh final state.  Moreover the transitions are made *canonical*: only one
transition is kept for each triple (source, letter, target).

The construction is sound for every code (`normCode_sound`: a run of the normal
form projects to a run of the original code), and complete whenever the relation
described by the code is a function on the strings over its alphabet
(`normCode_complete`).  Completeness uses that promise only at the very end:
what is proved directly is that *some* run of the normal form exists over every
nonempty string in the domain, and soundness together with functionality then
forces its output to be the right one.

The point of the normal form is that all the runs of `normCode c` over a string
`w` have exactly `|w|` transitions, so there are finitely many of them and they
can be enumerated (`RequestProject/PartB/RunList.lean`); canonicity makes a
transition of the synchronous product of two such codes recoverable from its
source, letter and target, which is what makes the runs of the product
automaton of `RequestProject/PartB/PairWeighted.lean` correspond to *pairs* of
runs.
-/
import Lax132576Proofs.Source.PartB.CodeAtom
import Lax132576Proofs.Source.PartB.LenDec
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace CodeMerge

open LabAut LenDec

/-- The type of coded transitions. -/
abbrev Tr := ℕ × List ℕ × List ℕ × ℕ

lemma inputOf_app (l₁ l₂ : List Tr) : inputOf (l₁ ++ l₂) = inputOf l₁ ++ inputOf l₂ := by
  simp [inputOf]

/-- Every transition reads at most one letter. -/
def InputAtomic (A : RelCode) : Prop := ∀ t ∈ A.1, t.2.1 = [] ∨ ∃ a, t.2.1 = [a]

/-- Every transition reads exactly one letter. -/
def LetterAtomic (M : RelCode) : Prop := ∀ t ∈ M.1, ∃ a, t.2.1 = [a]

/-- The source, the input string and the target of a transition. -/
def key (t : Tr) : ℕ × List ℕ × ℕ := (t.1, t.2.1, t.2.2.2)

/-- A code is canonical if a transition is determined by its source, its input
string and its target. -/
def Canonical (M : RelCode) : Prop := ∀ t ∈ M.1, ∀ t' ∈ M.1, key t = key t' → t = t'

/-! ## Removing duplicates

`List.dedup` is defined through `List.pwFilter`, for which Mathlib has no
`Primrec` lemma; the `foldr`-based version below is manifestly primitive
recursive. -/

/-- A `foldr`-based version of `List.dedup`. -/
def dedupB {α : Type} [DecidableEq α] (l : List α) : List α :=
  l.foldr (fun a r => if a ∈ r then r else a :: r) []

@[simp] lemma dedupB_nil {α : Type} [DecidableEq α] : dedupB ([] : List α) = [] := rfl

lemma dedupB_cons {α : Type} [DecidableEq α] (a : α) (l : List α) :
    dedupB (a :: l) = if a ∈ dedupB l then dedupB l else a :: dedupB l := rfl

@[simp] lemma mem_dedupB {α : Type} [DecidableEq α] {l : List α} {x : α} :
    x ∈ dedupB l ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [dedupB_cons]
      by_cases h : a ∈ dedupB l
      · rw [if_pos h]
        simp only [List.mem_cons, ih]
        constructor
        · exact fun hx => Or.inr hx
        · rintro (rfl | hx)
          · exact ih.1 h
          · exact hx
      · rw [if_neg h]
        simp [ih]

lemma dedupB_nodup {α : Type} [DecidableEq α] (l : List α) : (dedupB l).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [dedupB_cons]
      by_cases h : a ∈ dedupB l
      · rwa [if_pos h]
      · rw [if_neg h]
        exact List.nodup_cons.2 ⟨h, ih⟩

lemma dedupB_subset {α : Type} [DecidableEq α] {l : List α} {x : α} (h : x ∈ dedupB l) : x ∈ l :=
  mem_dedupB.1 h

/-! ## Making a list of transitions canonical -/

/-- Keep, among the transitions with a given source, input string and target,
the first one. -/
def canonize (L : List Tr) : List Tr :=
  (dedupB (L.map key)).filterMap (fun k => L.find? (fun t => decide (key t = k)))

lemma canonize_subset {L : List Tr} {t : Tr} (h : t ∈ canonize L) : t ∈ L := by
  rw [canonize, List.mem_filterMap] at h
  obtain ⟨k, -, hk⟩ := h
  exact List.mem_of_find?_eq_some hk

lemma canonize_key_eq {L : List Tr} {t : Tr} (h : t ∈ canonize L) :
    ∃ k ∈ dedupB (L.map key), L.find? (fun s => decide (key s = k)) = some t ∧ key t = k := by
  rw [canonize, List.mem_filterMap] at h
  obtain ⟨k, hk, hf⟩ := h
  refine ⟨k, hk, hf, ?_⟩
  have := List.find?_some hf
  simpa using this

lemma canonize_key {L : List Tr} {t : Tr} (h : t ∈ L) : ∃ t' ∈ canonize L, key t' = key t := by
  have hk : key t ∈ dedupB (L.map key) := mem_dedupB.2 (List.mem_map_of_mem h)
  have hfind : (L.find? (fun s => decide (key s = key t))).isSome := by
    rw [List.find?_isSome]
    exact ⟨t, h, by simp⟩
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 hfind
  refine ⟨t', ?_, ?_⟩
  · rw [canonize, List.mem_filterMap]
    exact ⟨key t, hk, ht'⟩
  · simpa using List.find?_some ht'

lemma canonize_canonical (L : List Tr) :
    ∀ t ∈ canonize L, ∀ t' ∈ canonize L, key t = key t' → t = t' := by
  intro t ht t' ht' hkey
  obtain ⟨k, -, hf, hk⟩ := canonize_key_eq ht
  obtain ⟨k', -, hf', hk'⟩ := canonize_key_eq ht'
  have : k = k' := by rw [← hk, ← hk', hkey]
  subst this
  rw [hf] at hf'
  exact Option.some_inj.1 hf'

lemma canonize_nodup (L : List Tr) : (canonize L).Nodup := by
  refine List.Nodup.filterMap ?_ (dedupB_nodup _)
  intro k k' t hk hk'
  have h1 : key t = k := by simpa using List.find?_some hk
  have h2 : key t = k' := by simpa using List.find?_some hk'
  rw [← h1, ← h2]

/-! ## The ε-transitions of an input-atomic code -/

lemma delta_iff (A : RelCode) : ∀ t, t ∈ (codeAut A).δ ↔ t ∈ A.1 := fun _ => Iff.rfl

lemma target_mem_state {A : RelCode} : ∀ t ∈ (codeAut A).δ, (t.2.2.2 : ℕ) ∈ stateList A :=
  target_mem_stateList A

/-- The automaton consisting of the ε-transitions of a code. -/
def epsAut (A : RelCode) : NFAO ℕ ℕ ℕ where
  init := ∅
  final := ∅
  δ := {t | t ∈ A.1 ∧ t.2.1 = []}
  δ_finite := Set.Finite.subset A.1.finite_toSet (fun _ ht => ht.1)

lemma path_of_eps {A : RelCode} {p q : ℕ} {ts : List Tr} (h : (epsAut A).Path p ts q) :
    (codeAut A).Path p ts q ∧ inputOf ts = [] := by
  induction h with
  | nil q => exact ⟨Path.nil q, rfl⟩
  | @cons q u l q' ts p ht _ ih =>
      obtain ⟨hmem, hnil⟩ := ht
      have hu : u = [] := hnil
      refine ⟨Path.cons hmem ih.1, ?_⟩
      simp [inputOf_cons, ih.2, hu]

lemma eps_of_path {A : RelCode} {p q : ℕ} {ts : List Tr} (h : (codeAut A).Path p ts q)
    (hin : inputOf ts = []) : (epsAut A).Path p ts q := by
  induction h with
  | nil q => exact Path.nil q
  | @cons q u l q' ts p ht _ ih =>
      rw [inputOf_cons] at hin
      have hu : u = [] := List.eq_nil_of_prefix_nil ⟨_, hin⟩
      refine Path.cons (show ((q, u, l, q') : Tr) ∈ (epsAut A).δ from ⟨ht, hu⟩) (ih ?_)
      rw [hu] at hin; simpa using hin

/-- An ε-path may be replaced by a short one with the same endpoints. -/
lemma eps_short {A : RelCode} {p q : ℕ} {ts : List Tr} (hp : p ∈ stateList A)
    (h : (codeAut A).Path p ts q) (hin : inputOf ts = []) :
    ∃ ts', (codeAut A).Path p ts' q ∧ inputOf ts' = [] ∧ ts'.length < (stateList A).length := by
  have hS : ∀ t ∈ (epsAut A).δ, (t.2.2.2 : ℕ) ∈ stateList A := fun t ht =>
    target_mem_stateList A t ht.1
  obtain ⟨ts', hts', hlen⟩ := Path.exists_short (stateList A) hS (eps_of_path h hin) hp
  obtain ⟨h1, h2⟩ := path_of_eps hts'
  exact ⟨ts', h1, h2, hlen⟩

/-- A path over a nonempty input splits at the transition reading its first
letter. -/
lemma peel (A : RelCode) (hat : InputAtomic A) :
    ∀ {ts : List Tr} {p r a : ℕ} {w' : List ℕ},
      (codeAut A).Path p ts r → inputOf ts = a :: w' →
      ∃ (e : List Tr) (t : Tr) (ts₂ : List Tr),
        inputOf e = [] ∧ t.2.1 = [a] ∧
          (codeAut A).Path p (e ++ [t]) t.2.2.2 ∧
          (codeAut A).Path t.2.2.2 ts₂ r ∧ inputOf ts₂ = w' := by
  intro ts
  induction ts with
  | nil => intro p r a w' _ hin; simp at hin
  | cons tr ts'' ih =>
      intro p r a w' hpath hin
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv hpath
      rw [inputOf_cons] at hin
      rcases hat tr hmem with hnil | ⟨b, hb⟩
      · rw [hnil] at hin
        simp only [List.nil_append] at hin
        obtain ⟨e, t, ts₂, he, ht, hp1, hp2, hin2⟩ := ih hrest hin
        refine ⟨tr :: e, t, ts₂, by simp [inputOf_cons, hnil, he], ht, ?_, hp2, hin2⟩
        have htr : ((tr.1, tr.2.1, tr.2.2.1, tr.2.2.2) : Tr) ∈ (codeAut A).δ := hmem
        rw [← hsrc]
        exact Path.cons htr hp1
      · rw [hb] at hin
        simp only [List.singleton_append, List.cons.injEq] at hin
        obtain ⟨rfl, hin2⟩ := hin
        refine ⟨[], tr, ts'', rfl, hb, ?_, hrest, hin2⟩
        have htr : ((tr.1, tr.2.1, tr.2.2.1, tr.2.2.2) : Tr) ∈ (codeAut A).δ := hmem
        rw [← hsrc]
        simpa using Path.cons htr (Path.nil tr.2.2.2)

/-! ## The normal form -/

/-- A state that does not occur in the code, used as the final state of the
normal form. -/
def freshF (A : RelCode) : ℕ :=
  (A.2.1 ++ A.2.2 ++ A.1.map (fun t => t.1) ++ A.1.map (fun t => t.2.2.2)).foldr max 0 + 1

lemma freshF_not_mem_stateList (A : RelCode) : freshF A ∉ stateList A := by
  intro h
  have hmem : freshF A ∈
      (A.2.1 ++ A.2.2 ++ A.1.map (fun t => t.1) ++ A.1.map (fun t => t.2.2.2)) := by
    simp only [stateList, List.mem_append] at h
    rcases h with h | h <;> simp [h]
  have := le_foldr_max hmem
  simp only [freshF] at this
  omega

/-- The length bound for the paths that are absorbed into one transition of the
normal form. -/
def segBound (A : RelCode) : ℕ := (stateList A).length + 1

/-- Does the transition sequence `ts` lead from `p` to a final state of `A`? -/
def endsFinal (A : RelCode) (p : ℕ) (ts : List Tr) : Bool :=
  ((runO A.1 p ts).map (fun q => memB A.2.2 q)).getD false

lemma endsFinal_iff (A : RelCode) (p : ℕ) (ts : List Tr) :
    endsFinal A p ts = true ↔ ∃ q ∈ A.2.2, (codeAut A).Path p ts q := by
  rw [endsFinal]
  rcases hrun : runO A.1 p ts with _ | q
  · simp only [Option.map_none, Option.getD_none, Bool.false_eq_true, false_iff]
    rintro ⟨q, -, hq⟩
    rw [(runO_iff A.1 (codeAut A) (delta_iff A) ts p q).2 hq] at hrun
    exact absurd hrun (by simp)
  · simp only [Option.map_some, Option.getD_some, memB_iff]
    constructor
    · intro hq
      exact ⟨q, hq, (runO_iff A.1 (codeAut A) (delta_iff A) ts p q).1 hrun⟩
    · rintro ⟨q', hq', hp'⟩
      rw [(runO_iff A.1 (codeAut A) (delta_iff A) ts p q').2 hp'] at hrun
      rw [Option.some_inj.1 hrun] at hq'
      exact hq'

/-- The transitions of the normal form that continue the run. -/
def contTrans (A : RelCode) : List Tr :=
  (stateList A).flatMap (fun p =>
    ((seqsUpto A.1 (segBound A)).filter (fun seg =>
        decide ((inputOf seg).length = 1) && (runO A.1 p seg).isSome)).map (fun seg =>
      (p, inputOf seg, NFAO.outputOf seg, (runO A.1 p seg).getD 0)))

/-- The transitions of the normal form that complete the run. -/
def finTrans (A : RelCode) : List Tr :=
  (stateList A).flatMap (fun p =>
    (seqsUpto A.1 (segBound A)).flatMap (fun seg =>
      ((seqsUpto A.1 (stateList A).length).filter (fun tail =>
          decide ((inputOf seg).length = 1) && decide (inputOf tail = []) &&
            endsFinal A p (seg ++ tail))).map (fun tail =>
        (p, inputOf seg, NFAO.outputOf seg ++ NFAO.outputOf tail, freshF A))))

/-- The letter-atomic code associated with an input-atomic code. -/
def merged (A : RelCode) : RelCode :=
  (canonize (contTrans A ++ finTrans A), dedupB A.2.1, [freshF A])

/-- The letter-atomic normal form of a code. -/
def normCode (c : RelCode) : RelCode := merged (CodeAtom.atomCode c)

/-! ## Basic properties of the transitions of the normal form -/

lemma mem_contTrans {A : RelCode} {tr : Tr} :
    tr ∈ contTrans A ↔ ∃ p ∈ stateList A, ∃ seg ∈ seqsUpto A.1 (segBound A),
      (inputOf seg).length = 1 ∧ (runO A.1 p seg).isSome = true ∧
        tr = (p, inputOf seg, NFAO.outputOf seg, (runO A.1 p seg).getD 0) := by
  simp only [contTrans, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, seg, ⟨hseg, hlen, hsome⟩, rfl⟩
    exact ⟨p, hp, seg, hseg, hlen, hsome, rfl⟩
  · rintro ⟨p, hp, seg, hseg, hlen, hsome, rfl⟩
    exact ⟨p, hp, seg, ⟨hseg, hlen, hsome⟩, rfl⟩

lemma mem_finTrans {A : RelCode} {tr : Tr} :
    tr ∈ finTrans A ↔ ∃ p ∈ stateList A, ∃ seg ∈ seqsUpto A.1 (segBound A),
      ∃ tail ∈ seqsUpto A.1 (stateList A).length,
        (inputOf seg).length = 1 ∧ inputOf tail = [] ∧ endsFinal A p (seg ++ tail) = true ∧
          tr = (p, inputOf seg, NFAO.outputOf seg ++ NFAO.outputOf tail, freshF A) := by
  simp only [finTrans, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, seg, hseg, tail, ⟨htail, ⟨hlen, hnil⟩, hfin⟩, rfl⟩
    exact ⟨p, hp, seg, hseg, tail, htail, hlen, hnil, hfin, rfl⟩
  · rintro ⟨p, hp, seg, hseg, tail, htail, hlen, hnil, hfin, rfl⟩
    exact ⟨p, hp, seg, hseg, tail, ⟨htail, ⟨hlen, hnil⟩, hfin⟩, rfl⟩

lemma contTrans_spec {A : RelCode} {tr : Tr} (h : tr ∈ contTrans A) :
    tr.1 ∈ stateList A ∧ tr.2.2.2 ∈ stateList A ∧ (∃ a, tr.2.1 = [a]) ∧
      NFAO.relFrom (codeAut A) tr.1 tr.2.1 tr.2.2.1 tr.2.2.2 := by
  obtain ⟨p, hp, seg, hseg, hlen, hsome, rfl⟩ := mem_contTrans.1 h
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsome
  have hpath : (codeAut A).Path p seg q := (runO_iff A.1 (codeAut A) (delta_iff A) seg p q).1 hq
  refine ⟨hp, ?_, ?_, ?_⟩
  · simp only [hq, Option.getD_some]
    exact Path.target_mem (stateList A) (target_mem_stateList A) hpath hp
  · rcases hu : inputOf seg with _ | ⟨a, u⟩
    · rw [hu] at hlen; simp at hlen
    · rcases u with _ | ⟨b, u⟩
      · exact ⟨a, rfl⟩
      · rw [hu] at hlen; simp at hlen
  · simp only [hq, Option.getD_some]
    exact ⟨seg, hpath, rfl, rfl⟩

lemma finTrans_spec {A : RelCode} {tr : Tr} (h : tr ∈ finTrans A) :
    tr.1 ∈ stateList A ∧ tr.2.2.2 = freshF A ∧ (∃ a, tr.2.1 = [a]) ∧
      ∃ q ∈ A.2.2, NFAO.relFrom (codeAut A) tr.1 tr.2.1 tr.2.2.1 q := by
  obtain ⟨p, hp, seg, hseg, tail, htail, hlen, hnil, hfin, rfl⟩ := mem_finTrans.1 h
  obtain ⟨q, hq, hpath⟩ := (endsFinal_iff A p (seg ++ tail)).1 hfin
  refine ⟨hp, rfl, ?_, q, hq, ?_⟩
  · rcases hu : inputOf seg with _ | ⟨a, u⟩
    · rw [hu] at hlen; simp at hlen
    · rcases u with _ | ⟨b, u⟩
      · exact ⟨a, rfl⟩
      · rw [hu] at hlen; simp at hlen
  · refine ⟨seg ++ tail, hpath, ?_, ?_⟩
    · show inputOf (seg ++ tail) = inputOf seg
      simp only [inputOf, List.map_append, List.flatten_append]
      simp only [inputOf] at hnil
      rw [hnil, List.append_nil]
    · simp [NFAO.outputOf, LabAut.labelsOf]

lemma merged_trans_mem {A : RelCode} {tr : Tr} (h : tr ∈ (merged A).1) :
    tr ∈ contTrans A ∨ tr ∈ finTrans A :=
  List.mem_append.1 (canonize_subset h)

lemma merged_src_mem {A : RelCode} {tr : Tr} (h : tr ∈ (merged A).1) : tr.1 ∈ stateList A := by
  rcases merged_trans_mem h with h' | h'
  · exact (contTrans_spec h').1
  · exact (finTrans_spec h').1

/-- Every transition of the normal form reads exactly one letter. -/
lemma merged_letterAtomic (A : RelCode) : LetterAtomic (merged A) := by
  intro tr h
  rcases merged_trans_mem h with h' | h'
  · exact (contTrans_spec h').2.2.1
  · exact (finTrans_spec h').2.2.1

lemma merged_canonical (A : RelCode) : Canonical (merged A) := canonize_canonical _

lemma merged_nodup (A : RelCode) : (merged A).1.Nodup := canonize_nodup _

lemma merged_init_nodup (A : RelCode) : (merged A).2.1.Nodup := dedupB_nodup _

lemma merged_init_not_final (A : RelCode) : ∀ q ∈ (merged A).2.1, q ∉ (merged A).2.2 := by
  intro q hq hq'
  have hq1 : q ∈ A.2.1 := dedupB_subset hq
  have : q = freshF A := by simpa [merged] using hq'
  exact freshF_not_mem_stateList A (this ▸ (by simp [stateList, hq1]))

/-- Every pair of a source and a letter with a transition of the normal form. -/
lemma exists_merged_trans {A : RelCode} {tr : Tr} (h : tr ∈ contTrans A ++ finTrans A) :
    ∃ y, ((tr.1, tr.2.1, y, tr.2.2.2) : Tr) ∈ (merged A).1 := by
  obtain ⟨tr', htr', hkey⟩ := canonize_key h
  refine ⟨tr'.2.2.1, ?_⟩
  simp only [key, Prod.mk.injEq] at hkey
  obtain ⟨h1, h2, h3⟩ := hkey
  rw [← h1, ← h2, ← h3]
  exact htr'

/-! ## Soundness -/

lemma merged_sound_aux (A : RelCode) : ∀ (ts : List Tr) (p : ℕ), p ∈ stateList A →
    (codeAut (merged A)).Path p ts (freshF A) →
    ∃ q ∈ A.2.2, NFAO.relFrom (codeAut A) p (inputOf ts) (NFAO.outputOf ts) q := by
  intro ts
  induction ts with
  | nil =>
      intro p hp hpath
      exact absurd (Path.eq_of_nil hpath ▸ hp) (freshF_not_mem_stateList A)
  | cons tr ts' ih =>
      intro p hp hpath
      obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv hpath
      have hmem' : tr ∈ (merged A).1 := hmem
      rcases merged_trans_mem hmem' with h' | h'
      · obtain ⟨-, htgt, -, hrel⟩ := contTrans_spec h'
        obtain ⟨q, hq, hrel2⟩ := ih tr.2.2.2 htgt hrest
        refine ⟨q, hq, ?_⟩
        rw [inputOf_cons, NFAO.outputOf_cons, ← hsrc]
        exact NFAO.relFrom_trans hrel hrel2
      · obtain ⟨-, htgt, -, q, hq, hrel⟩ := finTrans_spec h'
        rw [htgt] at hrest
        have hnil : ts' = [] := by
          rcases ts' with _ | ⟨tr2, ts2⟩
          · rfl
          · obtain ⟨hsrc2, hmem2, -⟩ := Path.cons_inv hrest
            exact absurd (hsrc2 ▸ merged_src_mem (show tr2 ∈ (merged A).1 from hmem2))
              (freshF_not_mem_stateList A)
        subst hnil
        refine ⟨q, hq, ?_⟩
        rw [inputOf_cons, NFAO.outputOf_cons, ← hsrc]
        simpa using hrel

lemma merged_sound (A : RelCode) {w v : List ℕ} (h : codeRel (merged A) w v) : codeRel A w v := by
  rw [codeRel, NFAO.rel_iff_relFrom] at h
  obtain ⟨q, hq, p, hp, ts, hpath, rfl, rfl⟩ := h
  have hq1 : q ∈ A.2.1 := dedupB_subset hq
  have hqS : q ∈ stateList A := by simp [stateList, hq1]
  have hpf : p = freshF A := by simpa [merged, codeAut] using hp
  subst hpf
  obtain ⟨r, hr, hrel⟩ := merged_sound_aux A ts q hqS hpath
  rw [codeRel, NFAO.rel_iff_relFrom]
  exact ⟨q, hq1, r, hr, hrel⟩
/-! ## Completeness -/

/-- Every path of an input-atomic code over a *nonempty* input word, ending in a
final state, is simulated by a path of the normal form ending in the fresh final
state.  The output is not controlled here; it is pinned down afterwards by
soundness together with functionality. -/
lemma merged_complete_aux (A : RelCode) (hat : InputAtomic A) :
    ∀ (w : List ℕ) (p : ℕ) (ts : List Tr) (r : ℕ), w ≠ [] → p ∈ stateList A →
      (codeAut A).Path p ts r → inputOf ts = w → r ∈ A.2.2 →
      ∃ x, NFAO.relFrom (codeAut (merged A)) p w x (freshF A) := by
  intro w
  induction w with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons a w' ih =>
    intro p ts r _ hp hpath hin hr
    obtain ⟨e, t, ts₂, he, ht, hp1, hp2, hin2⟩ := peel A hat hpath hin
    obtain ⟨r', hpe, hpt⟩ := Path.split_append hp1
    obtain ⟨hsrc, htδ, -⟩ := Path.cons_inv hpt
    subst hsrc
    obtain ⟨e', hpe', he', hlen'⟩ := eps_short hp hpe he
    have htδ' : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : Tr) ∈ (codeAut A).δ := htδ
    have hone : (codeAut A).Path t.1 [t] t.2.2.2 := by
      simpa using Path.cons htδ' (Path.nil t.2.2.2)
    set seg : List Tr := e' ++ [t] with hsegdef
    have hsegpath : (codeAut A).Path p seg t.2.2.2 := hpe'.append hone
    have hsegin : inputOf seg = [a] := by
      rw [hsegdef, inputOf_app, he']
      simp [inputOf, ht]
    have hsegmem : seg ∈ seqsUpto A.1 (segBound A) := by
      refine (mem_seqsUpto _ _ _).2 ⟨?_, ?_⟩
      · rw [hsegdef]; simp only [List.length_append, List.length_singleton, segBound]; omega
      · intro s hs; exact Path.mem_delta hsegpath s hs
    have hrunO : runO A.1 p seg = some t.2.2.2 :=
      (runO_iff A.1 (codeAut A) (delta_iff A) seg p _).2 hsegpath
    have ht22 : t.2.2.2 ∈ stateList A := target_mem_stateList A t htδ
    rcases w' with _ | ⟨b, w''⟩
    · -- last letter: use a completing transition
      obtain ⟨tail, htailpath, htailin, htaillen⟩ := eps_short ht22 hp2 hin2
      have htailmem : tail ∈ seqsUpto A.1 (stateList A).length :=
        (mem_seqsUpto _ _ _).2 ⟨le_of_lt htaillen, fun s hs => Path.mem_delta htailpath s hs⟩
      have hfin : endsFinal A p (seg ++ tail) = true :=
        (endsFinal_iff A p (seg ++ tail)).2 ⟨r, hr, hsegpath.append htailpath⟩
      have hmem0 : ((p, inputOf seg, NFAO.outputOf seg ++ NFAO.outputOf tail, freshF A) : Tr)
          ∈ finTrans A :=
        mem_finTrans.2 ⟨p, hp, seg, hsegmem, tail, htailmem, by rw [hsegin]; rfl, htailin,
          hfin, rfl⟩
      obtain ⟨y, hy⟩ := exists_merged_trans (List.mem_append_right _ hmem0)
      simp only [hsegin] at hy
      exact ⟨y, NFAO.relFrom_single (M := codeAut (merged A)) hy⟩
    · -- not the last letter: use a continuing transition
      obtain ⟨x, hx⟩ := ih t.2.2.2 ts₂ r (by simp) ht22 hp2 hin2 hr
      have hmem0 : ((p, inputOf seg, NFAO.outputOf seg, (runO A.1 p seg).getD 0) : Tr)
          ∈ contTrans A :=
        mem_contTrans.2 ⟨p, hp, seg, hsegmem, by rw [hsegin]; rfl, by rw [hrunO]; rfl, rfl⟩
      obtain ⟨y, hy⟩ := exists_merged_trans (List.mem_append_left _ hmem0)
      simp only [hsegin, hrunO, Option.getD_some] at hy
      exact ⟨y ++ x, NFAO.relFrom_step (M := codeAut (merged A)) hy hx⟩

/-- Over a nonempty input in the domain of an input-atomic code, the normal form
has at least one accepting run. -/
lemma merged_complete (A : RelCode) (hat : InputAtomic A) {w v : List ℕ}
    (h : codeRel A w v) (hw : w ≠ []) : ∃ x, codeRel (merged A) w x := by
  rw [codeRel, NFAO.rel_iff_relFrom] at h
  obtain ⟨q, hq, r, hr, ts, hpath, hin, -⟩ := h
  have hqS : q ∈ stateList A := init_mem_stateList A q hq
  obtain ⟨x, hx⟩ := merged_complete_aux A hat w q ts r hw hqS hpath hin hr
  refine ⟨x, ?_⟩
  rw [codeRel, NFAO.rel_iff_relFrom]
  exact ⟨q, mem_dedupB.2 hq, freshF A, by simp [codeAut, merged], hx⟩

/-! ## The normal form of an arbitrary code -/

lemma normCode_letterAtomic (c : RelCode) : LetterAtomic (normCode c) :=
  merged_letterAtomic _

lemma normCode_canonical (c : RelCode) : Canonical (normCode c) := merged_canonical _

lemma normCode_nodup (c : RelCode) : (normCode c).1.Nodup := merged_nodup _

lemma normCode_init_nodup (c : RelCode) : (normCode c).2.1.Nodup := merged_init_nodup _

lemma normCode_init_not_final (c : RelCode) :
    ∀ q ∈ (normCode c).2.1, q ∉ (normCode c).2.2 := merged_init_not_final _

/-- A run of the normal form projects to a run of the original code. -/
lemma normCode_sound (c : RelCode) {w v : List ℕ} (h : codeRel (normCode c) w v) :
    codeRel c w v := by
  rw [← CodeAtom.atomCode_rel c]
  exact merged_sound _ h

/-- Over a nonempty input in the domain, the normal form has an accepting run. -/
lemma normCode_complete (c : RelCode) {w v : List ℕ} (h : codeRel c w v) (hw : w ≠ []) :
    ∃ x, codeRel (normCode c) w x :=
  merged_complete _ (CodeAtom.atomCode_atomic c) (by rwa [CodeAtom.atomCode_rel]) hw

/-! ## Computability of the normal form

The normal form must be computable for the reduction of Theorem `thm:equivalence-rational-functions`
to Theorem `thm:equivalence-weighted-automata` to be effective.  All the ingredients are manifestly
primitive recursive; the proofs below are the usual combinator plumbing. -/

lemma filter_eq_filterMap {α : Type} (p : α → Bool) (l : List α) :
    l.filter p = l.filterMap (fun x => bif p x then some x else none) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih]

lemma find?_eq_head?_filter {α : Type} (p : α → Bool) (l : List α) :
    l.find? p = (l.filter p).head? := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.find?_cons, List.filter_cons]
      cases h : p a with
      | false => simp
      | true => simp

lemma primrec_filter {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).filter (p a)) := by
  refine (Primrec.listFilterMap hf
    (Primrec.cond hp (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)).to₂).of_eq ?_
  intro a
  exact (filter_eq_filterMap _ _).symm

lemma primrec_findQ {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).find? (p a)) :=
  (Primrec.list_head?.comp (primrec_filter hf hp)).of_eq
    (fun _ => (find?_eq_head?_filter _ _).symm)

lemma dedupB_eq_foldrB {α : Type} [DecidableEq α] (l : List α) :
    dedupB l = l.foldr (fun a r => bif memB r a then r else a :: r) [] := by
  refine congrArg (fun g => l.foldr g []) ?_
  funext a r
  cases hm : memB r a
  · have h : a ∉ r := fun hc => by rw [(memB_iff r a).2 hc] at hm; exact Bool.noConfusion hm
    simp [h]
  · have h : a ∈ r := (memB_iff r a).1 hm
    simp [h]

lemma primrec_dedupB {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (dedupB : List α → List α) := by
  refine (Primrec.list_foldr (h := fun (_ : List α) (q : α × List α) =>
      bif memB q.2 q.1 then q.2 else q.1 :: q.2)
    Primrec.id (Primrec.const []) ?_).of_eq (fun l => (dedupB_eq_foldrB l).symm)
  show Primrec fun w : List α × (α × List α) =>
    bif memB w.2.2 w.2.1 then w.2.2 else w.2.1 :: w.2.2
  exact Primrec.cond
    (primrec_memB.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

lemma primrec_key : Primrec key :=
  Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

lemma primrec_inputOf : Primrec (inputOf : List Tr → List ℕ) :=
  Primrec.list_flatten.comp
    (Primrec.list_map Primrec.id (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).to₂)

lemma primrec_outputOf : Primrec (NFAO.outputOf : List Tr → List ℕ) :=
  Primrec.list_flatten.comp
    (Primrec.list_map Primrec.id
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)

lemma primrec_canonize : Primrec canonize := by
  refine Primrec.listFilterMap ?_ ?_
  · exact primrec_dedupB.comp
      (Primrec.list_map Primrec.id (primrec_key.comp Primrec.snd).to₂)
  · exact primrec_findQ Primrec.fst
      (primrec_decEq (primrec_key.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))

lemma primrec_stateList : Primrec stateList :=
  Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.list_map Primrec.fst
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)

lemma primrec_segBound : Primrec segBound :=
  Primrec.succ.comp (Primrec.list_length.comp primrec_stateList)

lemma primrec_freshF : Primrec freshF := by
  have hlist : Primrec (fun A : RelCode =>
      A.2.1 ++ A.2.2 ++ A.1.map (fun t => t.1) ++ A.1.map (fun t => t.2.2.2)) := by
    refine Primrec.list_append.comp (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) ?_) ?_
    · exact Primrec.list_map Primrec.fst (Primrec.fst.comp Primrec.snd).to₂
    · exact Primrec.list_map Primrec.fst
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  refine Primrec.succ.comp ?_
  refine (Primrec.list_foldr (h := fun (_ : RelCode) (q : ℕ × ℕ) => max q.1 q.2)
    hlist (Primrec.const 0) ?_).of_eq (fun _ => rfl)
  show Primrec fun w : RelCode × (ℕ × ℕ) => max w.2.1 w.2.2
  exact Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)

lemma primrec_endsFinal :
    Primrec (fun z : (RelCode × ℕ) × List Tr => endsFinal z.1.1 z.1.2 z.2) := by
  refine Primrec.option_getD.comp ?_ (Primrec.const false)
  refine Primrec.option_map ?_ ?_
  · exact primrec_runO.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  · exact primrec_memB.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd

set_option maxHeartbeats 1000000 in
lemma primrec_contTrans : Primrec contTrans := by
  refine Primrec.list_flatMap primrec_stateList ?_
  -- ambient type: `RelCode × ℕ`
  have hseq : Primrec (fun z : RelCode × ℕ => seqsUpto z.1.1 (segBound z.1)) :=
    primrec_seqsUpto.comp (Primrec.fst.comp Primrec.fst) (primrec_segBound.comp Primrec.fst)
  have hrun : Primrec (fun z : (RelCode × ℕ) × List Tr => runO z.1.1.1 z.1.2 z.2) :=
    primrec_runO.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have hpred : Primrec₂ (fun (z : RelCode × ℕ) (seg : List Tr) =>
      decide ((inputOf seg).length = 1) && (runO z.1.1 z.2 seg).isSome) :=
    (Primrec.and.comp
      (primrec_decEq (Primrec.list_length.comp (primrec_inputOf.comp Primrec.snd))
        (Primrec.const 1))
      (Primrec.option_isSome.comp hrun)).to₂
  refine Primrec.list_map (primrec_filter hseq hpred) ?_
  exact (Primrec.pair (Primrec.snd.comp Primrec.fst)
    (Primrec.pair (primrec_inputOf.comp Primrec.snd)
      (Primrec.pair (primrec_outputOf.comp Primrec.snd)
        (Primrec.option_getD.comp hrun (Primrec.const 0))))).to₂

set_option maxHeartbeats 1000000 in
lemma primrec_finTrans : Primrec finTrans := by
  refine Primrec.list_flatMap primrec_stateList ?_
  -- ambient type: `RelCode × ℕ`
  have hseq : Primrec (fun z : RelCode × ℕ => seqsUpto z.1.1 (segBound z.1)) :=
    primrec_seqsUpto.comp (Primrec.fst.comp Primrec.fst) (primrec_segBound.comp Primrec.fst)
  refine Primrec.list_flatMap hseq ?_
  -- ambient type: `(RelCode × ℕ) × List Tr`
  have hseq2 : Primrec (fun z : (RelCode × ℕ) × List Tr =>
      seqsUpto z.1.1.1 (stateList z.1.1).length) :=
    primrec_seqsUpto.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_length.comp (primrec_stateList.comp (Primrec.fst.comp Primrec.fst)))
  have hpred : Primrec₂ (fun (z : (RelCode × ℕ) × List Tr) (tail : List Tr) =>
      decide ((inputOf z.2).length = 1) && decide (inputOf tail = []) &&
        endsFinal z.1.1 z.1.2 (z.2 ++ tail)) := by
    have h1 : Primrec (fun w : ((RelCode × ℕ) × List Tr) × List Tr =>
        decide ((inputOf w.1.2).length = 1)) :=
      primrec_decEq
        (Primrec.list_length.comp (primrec_inputOf.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const 1)
    have h2 : Primrec (fun w : ((RelCode × ℕ) × List Tr) × List Tr =>
        decide (inputOf w.2 = [])) :=
      primrec_decEq (primrec_inputOf.comp Primrec.snd) (Primrec.const ([] : List ℕ))
    have h3 : Primrec (fun w : ((RelCode × ℕ) × List Tr) × List Tr =>
        endsFinal w.1.1.1 w.1.1.2 (w.1.2 ++ w.2)) :=
      primrec_endsFinal.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
    have hkey : Primrec (fun w : ((RelCode × ℕ) × List Tr) × List Tr =>
        decide ((inputOf w.1.2).length = 1) && decide (inputOf w.2 = []) &&
          endsFinal w.1.1.1 w.1.1.2 (w.1.2 ++ w.2)) :=
      Primrec.and.comp (Primrec.and.comp h1 h2) h3
    exact hkey.to₂
  refine Primrec.list_map (primrec_filter hseq2 hpred) ?_
  exact (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.pair (primrec_inputOf.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.list_append.comp (primrec_outputOf.comp (Primrec.snd.comp Primrec.fst))
          (primrec_outputOf.comp Primrec.snd))
        (primrec_freshF.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))).to₂

lemma primrec_merged : Primrec merged :=
  Primrec.pair
    (primrec_canonize.comp (Primrec.list_append.comp primrec_contTrans primrec_finTrans))
    (Primrec.pair (primrec_dedupB.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp primrec_freshF (Primrec.const ([] : List ℕ))))

lemma primrec_normCode : Primrec normCode :=
  primrec_merged.comp CodeAtom.primrec_atomCode

end CodeMerge
end Lax132576Proofs.Transducers
