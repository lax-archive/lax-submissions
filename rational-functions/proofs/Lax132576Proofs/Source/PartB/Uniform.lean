/-
Uniformisation of rational relations (Lemma `lem:uniformisation`).

Let `R` be a total rational relation.  By Lemma `lemma:eliminate-epsilon-transitions` it is computed
by an automaton `N` with extended transitions (each transition is labelled by an input letter and a
regular language of output strings) in which every accepting run reads exactly one letter per
transition, except for the runs over the empty input, which consist of a single transition.

Choosing one output string in each (nonempty) language of a transition turns `N`
into an ordinary nfa with output `chosen N` whose relation is contained in `R`
and which is still total and ε-free.  By `exists_unambiguous_of_epsFree` it
contains an unambiguous nfa with output, which uniformises `R`.
-/
import Lax132576Proofs.Source.PartB.Unambig
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace Uniform

open LabAut NFAO

variable {A B Q : Type}

open scoped Classical in
/-- A choice of an output string in a language (the empty string if the language
is empty). -/
noncomputable def pick (L : Language B) : List B := if h : ∃ v, v ∈ L then h.choose else []

lemma pick_mem {L : Language B} (h : L.Nonempty) : pick L ∈ L := by
  classical
  have h' : ∃ v, v ∈ L := h
  rw [pick, dif_pos h']
  exact h'.choose_spec

/-- If a string belongs to the product of a list of languages, then all these
languages are nonempty. -/
lemma nonempty_of_mem_prod {Ls : List (Language B)} :
    ∀ {v : List B}, v ∈ Ls.prod → ∀ L ∈ Ls, L.Nonempty := by
  induction Ls with
  | nil => intro v _ L hL; simp at hL
  | cons L Ls ih =>
      intro v hv L' hL'
      rw [List.prod_cons, Language.mem_mul] at hv
      obtain ⟨x, hx, y, hy, -⟩ := hv
      rcases List.mem_cons.mp hL' with rfl | hmem
      · exact ⟨x, hx⟩
      · exact ih hy L' hmem

/-- The nfa with output obtained by choosing one output string in each
transition of an automaton with extended transitions. -/
noncomputable def chosen (N : LabAut A (Language B) Q) : NFAO A B Q where
  init := N.init
  final := N.final
  δ := (fun t : Q × List A × Language B × Q => (t.1, t.2.1, pick t.2.2.1, t.2.2.2)) ''
    {t ∈ N.δ | (t.2.2.1).Nonempty}
  δ_finite := Set.Finite.image _ (N.δ_finite.subset (fun _ ht => ht.1))

@[simp] lemma chosen_init (N : LabAut A (Language B) Q) : (chosen N).init = N.init := rfl

@[simp] lemma chosen_final (N : LabAut A (Language B) Q) : (chosen N).final = N.final := rfl

/-- Every run of `chosen N` comes from a run of `N` reading the same letters and
producing the chosen output. -/
lemma npath_of_chosenPath {N : LabAut A (Language B) Q} {q p : Q}
    {ts : List (Q × List A × List B × Q)} (h : (chosen N).Path q ts p) :
    ∃ ts', N.Path q ts' p ∧ ts'.map (fun t => t.2.1) = ts.map (fun t => t.2.1) ∧
      outputOf ts ∈ (labelsOf ts').prod := by
  induction h with
  | nil q => exact ⟨[], Path.nil q, rfl, by simp [Language.mem_one]⟩
  | @cons q u x q' ts p ht hpath ih =>
      obtain ⟨t, ⟨htδ, htne⟩, heq⟩ := ht
      obtain ⟨t1, u1, L1, q1⟩ := t
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, he3, rfl⟩ := heq
      obtain ⟨ts', hpath', hmap', hout'⟩ := ih
      refine ⟨(t1, u1, L1, q1) :: ts', Path.cons htδ hpath', by simp [hmap'], ?_⟩
      simp only [labelsOf_cons, List.prod_cons, Language.mem_mul, outputOf_cons]
      exact ⟨x, he3 ▸ pick_mem htne, outputOf ts, hout', rfl⟩

/-- Conversely, every run of `N` all of whose languages are nonempty gives a run
of `chosen N`. -/
lemma chosenPath_of_npath {N : LabAut A (Language B) Q} {q p : Q}
    {ts' : List (Q × List A × Language B × Q)} (h : N.Path q ts' p)
    (hne : ∀ t ∈ ts', (t.2.2.1).Nonempty) :
    ∃ ts, (chosen N).Path q ts p ∧ ts.map (fun t => t.2.1) = ts'.map (fun t => t.2.1) := by
  induction h with
  | nil q => exact ⟨[], Path.nil q, rfl⟩
  | @cons q u L q' ts' p ht hpath ih =>
      obtain ⟨ts, hpath', hmap⟩ := ih (fun t htm => hne t (by simp [htm]))
      refine ⟨(q, u, pick L, q') :: ts, ?_, by simp [hmap]⟩
      refine Path.cons ?_ hpath'
      exact ⟨(q, u, L, q'), ⟨ht, hne _ (by simp)⟩, rfl⟩

end Uniform

open LabAut NFAO Uniform in
/-- A total rational relation contains the relation of an unambiguous nfa with
output which is moreover ε-free. -/
theorem exists_unambiguous_epsFree_of_total {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (htotal : ∀ w, ∃ v, R w v) :
    ∃ (P : Type) (_ : Finite P) (N : NFAO A B P), N.Unambiguous ∧
      (∀ ts, N.Accepting ts →
        (inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧ (inputOf ts = [] → ts.length = 1)) ∧
      ∀ w v, N.rel w v → R w v := by
  classical
  obtain ⟨Q, hQ, N, -, hef, hrel⟩ := (epsilon_elimination_aux hR).1
  set M := chosen N with hM
  -- the relation of `M` is contained in `R`
  have hsub : ∀ w v, M.rel w v → R w v := by
    rintro w v ⟨ts, ⟨q₀, hq₀, q, hq, hpath⟩, hin, hout⟩
    obtain ⟨ts', hpath', hmap, hprod⟩ := npath_of_chosenPath hpath
    refine (hrel w v).mpr ⟨ts', ⟨q₀, hq₀, q, hq, hpath'⟩, ?_, ?_⟩
    · rw [show inputOf ts' = inputOf ts by simp [inputOf, hmap], hin]
    · rw [hout] at hprod; exact hprod
  -- `M` is total
  have htot : ∀ w, ∃ v, M.rel w v := by
    intro w
    obtain ⟨v, hv⟩ := htotal w
    obtain ⟨ts', ⟨q₀, hq₀, q, hq, hpath'⟩, hin', hprod⟩ := (hrel w v).mp hv
    have hne : ∀ t ∈ ts', (t.2.2.1).Nonempty := by
      intro t ht
      exact nonempty_of_mem_prod hprod t.2.2.1 (List.mem_map.mpr ⟨t, ht, rfl⟩)
    obtain ⟨ts, hpath, hmap⟩ := chosenPath_of_npath hpath' hne
    exact ⟨outputOf ts, ts, ⟨q₀, hq₀, q, hq, hpath⟩,
      by rw [show inputOf ts = inputOf ts' by simp [inputOf, hmap], hin'], rfl⟩
  -- `M` is ε-free
  have hefM : ∀ ts, M.Accepting ts →
      (inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧ (inputOf ts = [] → ts.length = 1) := by
    rintro ts ⟨q₀, hq₀, q, hq, hpath⟩
    obtain ⟨ts', hpath', hmap, -⟩ := npath_of_chosenPath hpath
    have hin : inputOf ts' = inputOf ts := by simp [inputOf, hmap]
    have hacc' : N.Accepting ts' := ⟨q₀, hq₀, q, hq, hpath'⟩
    obtain ⟨h1, h2⟩ := hef ts' hacc'
    constructor
    · intro hne t ht
      have : t.2.1 ∈ ts'.map (fun t => t.2.1) := by
        rw [hmap]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      obtain ⟨t', ht', heq⟩ := List.mem_map.mp this
      rw [← heq]
      exact h1 (by rw [hin]; exact hne) t' ht'
    · intro hnil
      have hlen : ts'.length = ts.length := by
        have := congrArg List.length hmap; simpa using this
      rw [← hlen]
      exact h2 (by rw [hin, hnil])
  obtain ⟨P, hP, N', hunamb, hefN, hincl⟩ := Unambig.exists_unambiguous_of_epsFree M hefM htot
  exact ⟨P, hP, N', hunamb, hefN, fun w v hwv => hsub w v (hincl w v hwv)⟩

/-- **Lemma `lem:uniformisation` (Uniformisation).**  A total rational relation contains an
unambiguous rational relation. -/
theorem uniformisation_aux {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (htotal : ∀ w, ∃ v, R w v) :
    ∃ S : List A → List B → Prop, (∀ w v, S w v → R w v) ∧ IsUnambiguousRel S := by
  obtain ⟨P, hP, N, hunamb, -, hincl⟩ := exists_unambiguous_epsFree_of_total hR htotal
  exact ⟨N.rel, hincl, P, hP, N, hunamb, fun w v => Iff.rfl⟩

open LabAut NFAO in
/-- A rational function is computed by an unambiguous ε-free nfa with output. -/
theorem exists_unambiguous_aut_of_rationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) :
    ∃ (P : Type) (_ : Finite P) (N : NFAO A B P), N.Unambiguous ∧
      (∀ ts, N.Accepting ts →
        (inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧ (inputOf ts = [] → ts.length = 1)) ∧
      ∀ w v, N.rel w v ↔ v = f w := by
  obtain ⟨P, hP, N, hunamb, hef, hincl⟩ :=
    exists_unambiguous_epsFree_of_total hf (fun w => ⟨f w, rfl⟩)
  refine ⟨P, hP, N, hunamb, hef, fun w v => ⟨hincl w v, ?_⟩⟩
  rintro rfl
  obtain ⟨ts, ⟨hacc, hin⟩, -⟩ := hunamb w
  have : N.rel w (outputOf ts) := ⟨ts, hacc, hin, rfl⟩
  rw [← hincl w _ this]
  exact this

end Lax132576Proofs.Transducers
